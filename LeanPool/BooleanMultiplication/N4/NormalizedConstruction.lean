/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Rewiring

/-!
# Construction of the rational three-gate prefix

The normalization is performed by algebraic basis replacement and legal gate
commutation.  No circuits are enumerated.  The only finite calculation below
is the three-coordinate proof that the rational place words are independent.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem rationalPlaceCoeff_linearIndependent :
    LinearIndependent F₂ rationalPlaceCoeff := by
  rw [Fintype.linearIndependent_iff]
  intro f h i
  have h0 := congrFun h (0 : Fin 7)
  have h1 := congrFun h (1 : Fin 7)
  have h6 := congrFun h (6 : Fin 7)
  simp only [rationalPlaceCoeff, rZeroCoeff, rOneCoeff, rInfinityCoeff, Fin.isValue,
    Finset.sum_apply, Pi.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, smul_eq_mul, Fin.sum_univ_succ, mul_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Finset.univ_unique, Fin.default_eq_zero, mul_zero,
    Finset.sum_const_zero, add_zero, Pi.zero_apply, Matrix.cons_val_one, zero_add,
    Matrix.cons_val, Finset.sum_singleton, Fin.succ_one_eq_two] at h0 h1 h6
  fin_cases i
  · rw [h1, add_zero] at h0
    exact h0
  · exact h1
  · rw [h1, zero_add] at h6
    exact h6

/-- A target coefficient outside a coefficient span remains outside after the
span is embedded as target ANFs and affine functions are adjoined. -/
theorem targetANF_not_mem_affine_sup_span {c : TargetCoeff}
    {S : Set TargetCoeff} (hc : c ∉ Submodule.span F₂ S) :
    targetANF c ∉
      affine 8 ⊔ Submodule.span F₂ (targetANF '' S) := by
  intro h
  rcases Submodule.mem_sup.mp h with ⟨a, ha, b, hb, hab⟩
  have hbRep : ∃ d : TargetCoeff,
      d ∈ Submodule.span F₂ S ∧ b = targetANF d := by
    refine Submodule.span_induction
      (p := fun b _ => ∃ d : TargetCoeff,
        d ∈ Submodule.span F₂ S ∧ b = targetANF d) ?_ ?_ ?_ ?_ hb
    · rintro q ⟨d, hd, rfl⟩
      exact ⟨d, Submodule.subset_span hd, rfl⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      change (0 : ANF 8) = targetANFLinear 0
      exact (map_zero targetANFLinear).symm
    · rintro p q _ _ ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      refine ⟨d + e, Submodule.add_mem _ hd he, ?_⟩
      change targetANFLinear d + targetANFLinear e = targetANFLinear (d + e)
      exact (map_add targetANFLinear d e).symm
    · rintro x p _ ⟨d, hd, rfl⟩
      refine ⟨x • d, Submodule.smul_mem _ x hd, ?_⟩
      change x • targetANFLinear d = targetANFLinear (x • d)
      exact (map_smul targetANFLinear x d).symm
  rcases hbRep with ⟨d, hd, rfl⟩
  have hproj := congrArg anfTwoProjection hab
  rw [map_add, anfTwoProjection_kills_affine ha,
    anfTwoProjection_targetANF, anfTwoProjection_targetANF, zero_add] at hproj
  have hdc : d = c := targetTwo_injective hproj
  exact hc (hdc ▸ hd)

theorem rOneANF_not_mem_affine_rZero :
    rOneANF ∉ affine 8 ⊔ Submodule.span F₂ {rZeroANF} := by
  have hc : rOneCoeff ∉ Submodule.span F₂ {rZeroCoeff} := by
    simpa [rationalPlaceCoeff] using
    (rationalPlaceCoeff_linearIndependent.notMem_span_image
      (s := ({0} : Set (Fin 3))) (x := 1) (by decide))
  simpa only [rZeroANF, rOneANF, Set.image_singleton] using
    (targetANF_not_mem_affine_sup_span (c := rOneCoeff)
      (S := {rZeroCoeff}) hc)

theorem rInfinityANF_not_mem_affine_rZero_rOne :
    rInfinityANF ∉
      affine 8 ⊔ Submodule.span F₂ {rZeroANF, rOneANF} := by
  have hc : rInfinityCoeff ∉
      Submodule.span F₂ {rZeroCoeff, rOneCoeff} := by
    simpa [Set.image_insert_eq, rationalPlaceCoeff] using
    (rationalPlaceCoeff_linearIndependent.notMem_span_image
      (s := ({0, 1} : Set (Fin 3))) (x := 2) (by decide))
  simpa only [rZeroANF, rOneANF, rInfinityANF, Set.image_insert_eq, Set.image_singleton] using
    (targetANF_not_mem_affine_sup_span (c := rInfinityCoeff)
      (S := {rZeroCoeff, rOneCoeff}) hc)

theorem wireSpace_one_eq_of_gate_zero {C : Circuit 8 8}
    (hzero : C.gate 0 = rZeroANF) :
    wireSpace C.gate 1 = affine 8 ⊔ Submodule.span F₂ {rZeroANF} := by
  rw [wireSpace_succ C.gate (by decide : 0 < 8), wireSpace_zero]
  have hidx : (⟨0, by decide⟩ : Fin 8) = 0 := Fin.ext rfl
  rw [hidx, hzero]

theorem wireSpace_two_eq_of_gate_zero_one {C : Circuit 8 8}
    (hzero : C.gate 0 = rZeroANF) (hone : C.gate 1 = rOneANF) :
    wireSpace C.gate 2 =
      affine 8 ⊔ Submodule.span F₂ {rZeroANF, rOneANF} := by
  rw [wireSpace_succ C.gate (by decide : 1 < 8),
    wireSpace_one_eq_of_gate_zero hzero]
  have hidx : (⟨1, by decide⟩ : Fin 8) = 1 := Fin.ext rfl
  rw [hidx, hone]
  rw [sup_assoc, ← Submodule.span_union]
  congr 2

/-- Every eight-gate circuit for four-bit multiplication can be transformed,
without changing its final wire space, so that its first three gates are the
three rational-place products. -/
theorem exists_rational_prefix (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) :
    ∃ D : Circuit 8 8,
      D.Computes (Mul 4) ∧
      D.finalWire = C.finalWire ∧
      D.gate 0 = rZeroANF ∧
      D.gate 1 = rOneANF ∧
      D.gate 2 = rInfinityANF := by
  have hmiss0 : targetANF (rationalPlaceCoeff 0) ∉ circuitFlag C 0 := by
    simpa [circuitFlag] using rationalPlaceANF_not_mem_affine (0 : Fin 3)
  rcases exists_promote_rational_place C hC 0 0 hmiss0 with
    ⟨C₀, hC₀, hfinal₀, hgate₀, _, _, _⟩
  have hzero : C₀.gate 0 = rZeroANF := by
    simpa [rationalPlaceCoeff, rZeroANF] using hgate₀
  have hmiss1 : targetANF (rationalPlaceCoeff 1) ∉ circuitFlag C₀ 1 := by
    rw [circuitFlag, wireSpace_one_eq_of_gate_zero hzero]
    simpa [rationalPlaceCoeff, rOneANF] using rOneANF_not_mem_affine_rZero
  rcases exists_promote_rational_place C₀ hC₀ 1 1 hmiss1 with
    ⟨C₁, hC₁, hfinal₁, hgate₁, _, _, hbefore₁⟩
  have hzero₁ : C₁.gate 0 = rZeroANF :=
    (hbefore₁ 0 (by decide)).trans hzero
  have hone₁ : C₁.gate 1 = rOneANF := by
    simpa [rationalPlaceCoeff, rOneANF] using hgate₁
  have hmiss2 : targetANF (rationalPlaceCoeff 2) ∉ circuitFlag C₁ 2 := by
    rw [circuitFlag, wireSpace_two_eq_of_gate_zero_one hzero₁ hone₁]
    simpa [rationalPlaceCoeff, rInfinityANF] using
      rInfinityANF_not_mem_affine_rZero_rOne
  rcases exists_promote_rational_place C₁ hC₁ 2 2 hmiss2 with
    ⟨D, hD, hfinal₂, hgate₂, _, _, hbefore₂⟩
  have hzeroD : D.gate 0 = rZeroANF :=
    (hbefore₂ 0 (by decide)).trans hzero₁
  have honeD : D.gate 1 = rOneANF :=
    (hbefore₂ 1 (by decide)).trans hone₁
  have hinfinityD : D.gate 2 = rInfinityANF := by
    simpa [rationalPlaceCoeff, rInfinityANF] using hgate₂
  exact ⟨D, hD, hfinal₂.trans (hfinal₁.trans hfinal₀),
    hzeroD, honeD, hinfinityD⟩

theorem rationalLowSpace_le_targetAmbient :
    rationalLowSpace ≤ targetAmbient 8 (mulTarget 4) := by
  apply sup_le le_sup_left
  apply le_sup_of_le_right
  rw [rationalTargetSpace, Submodule.span_le]
  rintro p (rfl | rfl | rfl)
  · exact targetANF_mem_mulTarget rZeroCoeff
  · exact targetANF_mem_mulTarget rOneCoeff
  · exact targetANF_mem_mulTarget rInfinityCoeff

theorem prefixGates_three_eq_of_rational_prefix {C : Circuit 8 8}
    (hzero : C.gate 0 = rZeroANF)
    (hone : C.gate 1 = rOneANF)
    (hinfinity : C.gate 2 = rInfinityANF) :
    prefixGates C.gate 3 = {rZeroANF, rOneANF, rInfinityANF} := by
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, hzero⟩
    · exact ⟨1, by decide, hone⟩
    · exact ⟨2, by decide, hinfinity⟩

theorem wireSpace_three_eq_of_rational_prefix {C : Circuit 8 8}
    (hzero : C.gate 0 = rZeroANF)
    (hone : C.gate 1 = rOneANF)
    (hinfinity : C.gate 2 = rInfinityANF) :
    wireSpace C.gate 3 = rationalLowSpace := by
  rw [wireSpace,
    prefixGates_three_eq_of_rational_prefix hzero hone hinfinity]
  rfl

/-- If a state already lies in the target ambient, adjoining a vector outside
that ambient does not change its intersection with the ambient. -/
theorem inf_sup_span_eq_left_of_le_of_not_mem
    (V A : Submodule F₂ (ANF 8)) (g : ANF 8)
    (hVA : V ≤ A) (hg : g ∉ A) :
    (V ⊔ Submodule.span F₂ {g}) ⊓ A = V := by
  apply le_antisymm
  · rintro p ⟨hp, hpA⟩
    rcases Submodule.mem_sup.mp hp with ⟨v, hv, w, hw, rfl⟩
    rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with rfl | rfl
    · simpa using hv
    · exfalso
      apply hg
      have hvg : v + g ∈ A := by simpa using hpA
      have hsum : (v + g) + v ∈ A :=
        Submodule.add_mem _ hvg (hVA hv)
      have heq : (v + g) + v = g := by
        calc
          (v + g) + v = (v + v) + g := by ac_rfl
          _ = g := by simp
      rwa [heq] at hsum
  · intro p hp
    exact ⟨Submodule.mem_sup_left hp, hVA hp⟩

theorem useful_gate_mem_targetAmbient_of_prefix_le
    (C : Circuit 8 8) (j : Fin 8)
    (hprefix : circuitFlag C j.val ≤ targetAmbient 8 (mulTarget 4))
    (huse : UsefulAt C (mulTarget 4) j) :
    C.gate j ∈ targetAmbient 8 (mulTarget 4) := by
  by_contra hg
  have hinter := inf_sup_span_eq_left_of_le_of_not_mem
    (circuitFlag C j.val) (targetAmbient 8 (mulTarget 4))
    (C.gate j) hprefix hg
  have hstep : circuitFlag C (j.val + 1) =
      circuitFlag C j.val ⊔ Submodule.span F₂ {C.gate j} := by
    rw [circuitFlag, wireSpace_succ C.gate j.isLt]
    congr 2
  unfold UsefulAt flagTargetRank at huse
  rw [hstep, hinter, inf_eq_left.mpr hprefix] at huse
  omega

theorem flagTargetRank_mono_of_affine_le {V W T : Submodule F₂ (ANF 8)}
    (hAffV : affine 8 ≤ V) (hVW : V ≤ W) :
    flagTargetRank V T ≤ flagTargetRank W T := by
  have hInf : V ⊓ targetAmbient 8 T ≤ W ⊓ targetAmbient 8 T :=
    fun _ hp => ⟨hVW hp.1, hp.2⟩
  have hdim := Submodule.finrank_mono hInf
  have hbase : Module.finrank F₂ ↥(affine 8) ≤
      Module.finrank F₂ ↥(V ⊓ targetAmbient 8 T) := by
    apply Submodule.finrank_mono
    intro p hp
    exact ⟨hAffV hp, Submodule.mem_sup_left hp⟩
  unfold flagTargetRank
  omega

theorem flagDefectRank_eq_zero_of_le {V T : Submodule F₂ (ANF 8)}
    (hV : V ≤ targetAmbient 8 T) :
    flagDefectRank V T = 0 := by
  unfold flagDefectRank
  rw [inf_eq_left.mpr hV]
  omega

/-- In a rationally prefixed multiplier the fourth gate is the unique defect
gate: if it were useful, its output would lie in the target ambient, and the
low-product bridge would make it redundant. -/
theorem rational_prefix_seed_not_useful (C : Circuit 8 8)
    (hC : C.Computes (Mul 4))
    (hzero : C.gate 0 = rZeroANF)
    (hone : C.gate 1 = rOneANF)
    (hinfinity : C.gate 2 = rInfinityANF) :
    ¬ UsefulAt C (mulTarget 4) 3 := by
  intro huse
  have hwire : circuitFlag C 3 = rationalLowSpace :=
    wireSpace_three_eq_of_rational_prefix hzero hone hinfinity
  have hprefix : circuitFlag C 3 ≤ targetAmbient 8 (mulTarget 4) := by
    rw [hwire]
    exact rationalLowSpace_le_targetAmbient
  have hgateAmbient := useful_gate_mem_targetAmbient_of_prefix_le C 3 hprefix huse
  have hleft : C.left 3 ∈ rationalLowSpace := by
    rw [← hwire]
    exact C.left_mem 3
  have hright : C.right 3 ∈ rationalLowSpace := by
    rw [← hwire]
    exact C.right_mem 3
  have hgateLow : C.gate 3 ∈ rationalLowSpace := by
    rw [C.gate_eq 3]
    exact rationalLow_mul_mem_of_mem_targetAmbient hleft hright
      (by simpa [C.gate_eq 3] using hgateAmbient)
  exact (eight_gate_all_nonredundant C hC 3) (by simpa [hwire] using hgateLow)

/-- Once the rational prefix and its non-useful seed account for the unique
defect, the four remaining gates must each buy exactly one target dimension. -/
theorem rational_prefix_suffix_useful (C : Circuit 8 8)
    (hC : C.Computes (Mul 4))
    (hzero : C.gate 0 = rZeroANF)
    (hone : C.gate 1 = rOneANF)
    (hinfinity : C.gate 2 = rInfinityANF)
    (hseed : ¬ UsefulAt C (mulTarget 4) 3) :
    ∀ j : Fin 8, 4 ≤ j.val → UsefulAt C (mulTarget 4) j := by
  let t : Nat → Nat := fun k => flagTargetRank (circuitFlag C k) (mulTarget 4)
  have hnr := eight_gate_all_nonredundant C hC
  have hwire : circuitFlag C 3 = rationalLowSpace :=
    wireSpace_three_eq_of_rational_prefix hzero hone hinfinity
  have hdef3 : flagDefectRank (circuitFlag C 3) (mulTarget 4) = 0 := by
    apply flagDefectRank_eq_zero_of_le
    rw [hwire]
    exact rationalLowSpace_le_targetAmbient
  have hcount3 := circuit_flag_defect_count C (mulTarget 4)
    (j := 3) (by decide) (by intro i _; exact hnr i)
  have ht3 : t 3 = 3 := by
    dsimp [t]
    rw [hdef3] at hcount3
    omega
  have hmono (a b : Nat) (hab : a ≤ b) : t a ≤ t b := by
    apply flagTargetRank_mono_of_affine_le
    · exact affine_le_wireSpace C.gate
    · exact wireSpace_mono hab
  have hstep (j : Fin 8) : t (j.val + 1) ≤ t j.val + 1 :=
    flagTargetRank_step_le_one C (mulTarget 4) j
  have ht4 : t 4 = 3 := by
    have hm := hmono 3 4 (by omega)
    have hs : t 4 ≤ t 3 + 1 := by
      simpa using hstep (3 : Fin 8)
    have hn : t 4 ≠ t 3 + 1 := by
      simpa [UsefulAt, t] using hseed
    omega
  have ht8 : t 8 = 7 := by
    dsimp [t]
    exact final_target_rank_four C hC
  have hm45 := hmono 4 5 (by omega)
  have hm56 := hmono 5 6 (by omega)
  have hm67 := hmono 6 7 (by omega)
  have hm78 := hmono 7 8 (by omega)
  have hs4 : t 5 ≤ t 4 + 1 := by simpa using hstep (4 : Fin 8)
  have hs5 : t 6 ≤ t 5 + 1 := by simpa using hstep (5 : Fin 8)
  have hs6 : t 7 ≤ t 6 + 1 := by simpa using hstep (6 : Fin 8)
  have hs7 : t 8 ≤ t 7 + 1 := by simpa using hstep (7 : Fin 8)
  have hu4 : t 5 = t 4 + 1 := by omega
  have hu5 : t 6 = t 5 + 1 := by omega
  have hu6 : t 7 = t 6 + 1 := by omega
  have hu7 : t 8 = t 7 + 1 := by omega
  intro j hj
  fin_cases j
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
  · simpa [UsefulAt, t] using hu4
  · simpa [UsefulAt, t] using hu5
  · simpa [UsefulAt, t] using hu6
  · simpa [UsefulAt, t] using hu7

/-- Closed normalized-eight-gate construction used by the structural proof. -/
theorem exists_normalized_eight (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) :
    ∃ D : Circuit 8 8, NormalizedEight D := by
  rcases exists_rational_prefix C hC with
    ⟨D, hD, _hfinal, hzero, hone, hinfinity⟩
  have hseed := rational_prefix_seed_not_useful D hD hzero hone hinfinity
  have hsuffix := rational_prefix_suffix_useful D hD hzero hone hinfinity hseed
  exact ⟨D, ⟨hD, hzero, hone, hinfinity, hseed, hsuffix,
    eight_gate_defect_is_one_algebraic D hD⟩⟩

end

end N4
end UnrestrictedBooleanMul
