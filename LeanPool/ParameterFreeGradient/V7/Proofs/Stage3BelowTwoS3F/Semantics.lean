/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Shapes

namespace V7.Stage3BelowTwoS3F

noncomputable local instance semanticsPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

theorem phaseOneTrace_succ (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    phaseOneNewTrace p eps M D x0 oracle (k + 1) =
      phaseOneNewTrace p eps M D x0 oracle k ++
        [phaseOneObs p eps M D x0 oracle (k + 1)] := by
  simp [phaseOneNewTrace, List.range_succ]

theorem phaseTwoTrace_succ (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    phaseTwoNewTrace p eps M D x0 oracle (k + 1) =
      phaseTwoNewTrace p eps M D x0 oracle k ++
        [phaseTwoObs p eps M D x0 oracle (k + 1)] := by
  simp [phaseTwoNewTrace, List.range_succ]

theorem phaseOneChecks_succ (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    phaseOneChecks p eps M D x0 oracle (k + 1) =
      phaseOneChecks p eps M D x0 oracle k ++
        [cocoCheck (phaseOneObs p eps M D x0 oracle k)
          (phaseOneObs p eps M D x0 oracle (k + 1))] := by
  simp [phaseOneChecks, List.range_succ]

theorem phaseTwoChecks_succ (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    phaseTwoChecks p eps M D x0 oracle (k + 1) =
      phaseTwoChecks p eps M D x0 oracle k ++
        [cocoCheck (phaseTwoObs p eps M D x0 oracle k)
          (phaseTwoObs p eps M D x0 oracle (k + 1))] := by
  simp [phaseTwoChecks, List.range_succ]

theorem normalizedGradient_phaseOne (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    normalizedGradient M D (phaseOneObs p eps M D x0 oracle k) =
      (phaseOneOracle x0 M D oracle).gradient
        (phaseOneState p eps M D x0 oracle k).x := by
  rfl

theorem phaseOneState_succ (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    phaseOneState p eps M D x0 oracle (k + 1) =
      let state := phaseOneState p eps M D x0 oracle k
      let sNext := state.s - increment (horizon p eps M D) k •
        normalizedGradient M D (phaseOneObs p eps M D x0 oracle k)
      let vNext := belowMirrorMap p sNext
      let xNext :=
        (weight (horizon p eps M D) k /
          weight (horizon p eps M D) (k + 1)) • state.x +
        (increment (horizon p eps M D) (k + 1) /
          weight (horizon p eps M D) (k + 1)) • vNext +
        (increment (horizon p eps M D) k /
          weight (horizon p eps M D) (k + 1)) • (vNext - state.v)
      ⟨sNext, vNext, xNext⟩ := by
  unfold phaseOneState
  rw [primalState_succ]
  rw [normalizedGradient_phaseOne]
  rfl

@[simp] theorem phaseTwoObs_zero (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) :
    phaseTwoObs p eps M D x0 oracle 0 = phaseOneObs p eps M D x0 oracle
      (horizon p eps M D) := by
  simp [phaseTwoObs, phaseTwoCenter, phaseOneObs, O3.PairOracle.observe]

theorem normalizedGradient_phaseTwo (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) :
    normalizedGradient M D (phaseTwoObs p eps M D x0 oracle k) =
      (phaseTwoOracle p eps M D x0 oracle).gradient
        (dualQ p (horizon p eps M D)
          (phaseTwoOracle p eps M D x0 oracle) k) := by
  rfl

theorem phaseTwoGradient_zero (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) :
    (phaseTwoOracle p eps M D x0 oracle).gradient 0 =
      normalizedGradient M D
        (phaseOneObs p eps M D x0 oracle (horizon p eps M D)) := by
  simp [phaseTwoOracle, phaseTwoCenter, normalizedPairOracle,
    normalizedGradient, phaseOneObs, O3.PairOracle.observe]

theorem eval_dual_shape (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k fuel : ℕ) (G : VectorSeq d)
    (horizonEq : k + fuel = horizon p eps M D)
    (hP : ∀ j < horizon p eps M D, cocoPairHolds p M
      (phaseOneObs p eps M D x0 oracle j)
      (phaseOneObs p eps M D x0 oracle (j + 1)))
    (hQ : ∀ j < k, cocoPairHolds p M
      (phaseTwoObs p eps M D x0 oracle j)
      (phaseTwoObs p eps M D x0 oracle (j + 1)))
    (hG : ∀ i ≤ k, G i =
      (phaseTwoOracle p eps M D x0 oracle).gradient
        (dualQ p (horizon p eps M D)
          (phaseTwoOracle p eps M D x0 oracle) i))
    (hlarge : eps < lpNorm (conjugateExponent p)
      (phaseTwoObs p eps M D x0 oracle k).gradient) :
    let n := horizon p eps M D
    let oracle₂ := phaseTwoOracle p eps M D x0 oracle
    ∃ m₁ m₂, FullShape p eps M D x0 oracle
      (Program.eval oracle fuel
        (dualProgram p eps M D n k (phaseTwoCenter p eps M D x0 oracle)
          (dualQ p n oracle₂ k) (dualR p n oracle₂ k) G
          (phaseTwoObs p eps M D x0 oracle k)
          (allChecks p eps M D x0 oracle n k) fuel)
        (phaseOneNewTrace p eps M D x0 oracle n ++
          phaseTwoNewTrace p eps M D x0 oracle k)) m₁ m₂ := by
  dsimp only
  induction fuel generalizing k G with
  | zero =>
      have hk : k = horizon p eps M D := by omega
      subst k
      exact ⟨horizon p eps M D, horizon p eps M D,
        FullShape.radius hP hQ hlarge⟩
  | succ fuel ih =>
      have hklt : k < horizon p eps M D := by omega
      rw [dualProgram, Program.eval]
      let n := horizon p eps M D
      let oracle₂ := phaseTwoOracle p eps M D x0 oracle
      let qNext := dualQ p n oracle₂ k -
        increment n (n - 1 - k) • belowMirrorMap p (dualR p n oracle₂ k)
      have hqNext : qNext = dualQ p n oracle₂ (k + 1) := by
        dsimp [qNext]
        rw [dualQ_succ]
      have hobs : oracle.observe (phaseTwoCenter p eps M D x0 oracle + D • qNext) =
          phaseTwoObs p eps M D x0 oracle (k + 1) := by
        rw [hqNext]
        rfl
      rw [hobs]
      by_cases hsmall : lpNorm (conjugateExponent p)
          (phaseTwoObs p eps M D x0 oracle (k + 1)).gradient ≤ eps
      · rw [if_pos hsmall]
        have hm0 : 0 < k + 1 := by omega
        have hmn : k + 1 ≤ horizon p eps M D := by omega
        refine ⟨horizon p eps M D, k + 1, ?_⟩
        simpa [Program.eval, phaseTwoTrace_succ, allChecks, phaseTwoChecks_succ,
          Nat.add_sub_cancel] using FullShape.dualSuccess (p := p) (eps := eps)
            (M := M) (D := D) (x0 := x0) (oracle := oracle)
            (k + 1) hm0 hmn hP (by
              intro j hj
              exact hQ j (by omega)) hsmall
      · rw [if_neg hsmall]
        have hlargeNext : eps < lpNorm (conjugateExponent p)
            (phaseTwoObs p eps M D x0 oracle (k + 1)).gradient :=
          lt_of_not_ge hsmall
        by_cases hguard : cocoPairHolds p M
            (phaseTwoObs p eps M D x0 oracle k)
            (phaseTwoObs p eps M D x0 oracle (k + 1))
        · rw [if_pos hguard]
          let GNext : VectorSeq d := fun i => if i = k + 1 then
                normalizedGradient M D (phaseTwoObs p eps M D x0 oracle (k + 1))
              else G i
          have hGNext : ∀ i ≤ k + 1, GNext i =
              (phaseTwoOracle p eps M D x0 oracle).gradient
                (dualQ p (horizon p eps M D)
                  (phaseTwoOracle p eps M D x0 oracle) i) := by
            intro i hi
            by_cases hieq : i = k + 1
            · subst i
              simp [GNext, normalizedGradient_phaseTwo]
            · simp [GNext, hieq, hG i (by omega)]
          have hrNext : dualR p (horizon p eps M D)
              (phaseTwoOracle p eps M D x0 oracle) k -
                weightedSum (k + 2)
                  (fun i => coeffB (horizon p eps M D)
                    (horizon p eps M D - i) (horizon p eps M D - 1 - k))
                  GNext =
              dualR p (horizon p eps M D)
                (phaseTwoOracle p eps M D x0 oracle) (k + 1) := by
            rw [dualR_succ]
            congr 1
            ext j
            simp only [weightedSum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hGNext i (by have := Finset.mem_range.mp hi; omega)]
          have hQnext : ∀ j < k + 1, cocoPairHolds p M
              (phaseTwoObs p eps M D x0 oracle j)
              (phaseTwoObs p eps M D x0 oracle (j + 1)) := by
            intro j hj
            by_cases hjk : j = k
            · subst j; exact hguard
            · exact hQ j (by omega)
          have hrec := ih (k + 1) GNext (by omega) hQnext hGNext hlargeNext
          simpa [dualQ_succ, GNext, hrNext, phaseTwoTrace_succ, allChecks,
            phaseTwoChecks_succ, List.append_assoc] using hrec
        · rw [if_neg hguard]
          have hm0 : 0 < k + 1 := by omega
          have hmn : k + 1 ≤ horizon p eps M D := by omega
          refine ⟨horizon p eps M D, k + 1, ?_⟩
          simpa [Program.eval, phaseTwoTrace_succ, allChecks, phaseTwoChecks_succ,
            List.append_assoc, Nat.add_sub_cancel] using
            FullShape.dualScale (p := p) (eps := eps) (M := M) (D := D)
              (x0 := x0) (oracle := oracle) (k + 1) hm0 hmn hP
              (by intro j hj; exact hQ j (by omega)) hlargeNext hguard

theorem eval_phaseOne_shape (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k fuel : ℕ)
    (horizonEq : k + fuel = horizon p eps M D)
    (hP : ∀ j < k, cocoPairHolds p M
      (phaseOneObs p eps M D x0 oracle j)
      (phaseOneObs p eps M D x0 oracle (j + 1)))
    (hlarge : eps < lpNorm (conjugateExponent p)
      (phaseOneObs p eps M D x0 oracle k).gradient) :
    ∃ m₁ m₂, FullShape p eps M D x0 oracle
      (Program.eval oracle (phaseOneBudget (horizon p eps M D) fuel)
        (phaseOneProgram p eps M D x0 (horizon p eps M D) k
          (phaseOneState p eps M D x0 oracle k)
          (phaseOneObs p eps M D x0 oracle k)
          (phaseOneChecks p eps M D x0 oracle k) fuel)
        (phaseOneNewTrace p eps M D x0 oracle k)) m₁ m₂ := by
  induction fuel generalizing k with
  | zero =>
      have hk : k = horizon p eps M D := by omega
      subst k
      let G0 := normalizedGradient M D
        (phaseOneObs p eps M D x0 oracle (horizon p eps M D))
      let G : VectorSeq d := fun i => if i = 0 then G0 else 0
      have hG0 : ∀ i ≤ 0, G i =
          (phaseTwoOracle p eps M D x0 oracle).gradient
            (dualQ p (horizon p eps M D)
              (phaseTwoOracle p eps M D x0 oracle) i) := by
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simp [G, G0, phaseTwoGradient_zero]
      have hdual := eval_dual_shape p eps M D x0 oracle 0
        (horizon p eps M D) G (by omega) hP (by simp) hG0 (by
          simpa using hlarge)
      simpa [phaseOneProgram, phaseOneBudget, G, G0, allChecks,
        phaseTwoNewTrace, phaseTwoChecks, phaseTwoObs_zero, dualQ_zero, dualR_zero,
        phaseTwoGradient_zero, phaseTwoCenter] using hdual
  | succ fuel ih =>
      have hklt : k < horizon p eps M D := by omega
      simp only [phaseOneBudget]
      rw [phaseOneProgram, Program.eval]
      have hobs : oracle.observe
          (x0 + D • (let state := phaseOneState p eps M D x0 oracle k
            let sNext := state.s - increment (horizon p eps M D) k •
              normalizedGradient M D (phaseOneObs p eps M D x0 oracle k)
            let vNext := belowMirrorMap p sNext
            let xNext :=
              (weight (horizon p eps M D) k /
                weight (horizon p eps M D) (k + 1)) • state.x +
              (increment (horizon p eps M D) (k + 1) /
                weight (horizon p eps M D) (k + 1)) • vNext +
              (increment (horizon p eps M D) k /
                weight (horizon p eps M D) (k + 1)) • (vNext - state.v)
            xNext)) = phaseOneObs p eps M D x0 oracle (k + 1) := by
        change oracle.observe _ = oracle.observe
          (x0 + D • (phaseOneState p eps M D x0 oracle (k + 1)).x)
        rw [phaseOneState_succ]
      rw [hobs]
      by_cases hsmall : lpNorm (conjugateExponent p)
          (phaseOneObs p eps M D x0 oracle (k + 1)).gradient ≤ eps
      · rw [if_pos hsmall]
        refine ⟨k + 1, 0, ?_⟩
        simpa [Program.eval, phaseOneTrace_succ, phaseOneChecks_succ,
          Nat.add_sub_cancel] using
          FullShape.primalSuccess (p := p) (eps := eps) (M := M) (D := D)
            (x0 := x0) (oracle := oracle) (k + 1) (by omega) (by omega)
            hsmall (by intro j hj; exact hP j (by omega))
      · rw [if_neg hsmall]
        have hlargeNext : eps < lpNorm (conjugateExponent p)
            (phaseOneObs p eps M D x0 oracle (k + 1)).gradient :=
          lt_of_not_ge hsmall
        by_cases hguard : cocoPairHolds p M
            (phaseOneObs p eps M D x0 oracle k)
            (phaseOneObs p eps M D x0 oracle (k + 1))
        · rw [if_pos hguard]
          have hPnext : ∀ j < k + 1, cocoPairHolds p M
              (phaseOneObs p eps M D x0 oracle j)
              (phaseOneObs p eps M D x0 oracle (j + 1)) := by
            intro j hj
            by_cases hjk : j = k
            · subst j; exact hguard
            · exact hP j (by omega)
          have hrec := ih (k + 1) (by omega) hPnext hlargeNext
          simpa [phaseOneState_succ, phaseOneTrace_succ, phaseOneChecks_succ]
            using hrec
        · rw [if_neg hguard]
          refine ⟨k + 1, 0, ?_⟩
          simpa [Program.eval, phaseOneTrace_succ, phaseOneChecks_succ,
            Nat.add_sub_cancel] using
            FullShape.primalScale (p := p) (eps := eps) (M := M) (D := D)
              (x0 := x0) (oracle := oracle) (k + 1) (by omega) (by omega)
              (by intro j hj; exact hP j (by omega)) hlargeNext hguard

end V7.Stage3BelowTwoS3F
