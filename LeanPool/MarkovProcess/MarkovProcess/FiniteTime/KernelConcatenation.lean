/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelRestriction
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

/-- Reassociate the cardinality of a split finite path so recursion removes its first point
definitionally while the coordinate order remains past-then-future. -/
def cutIndexOrderIso (m n : ℕ) : Fin ((m + 1) + n) ≃o Fin (n + (m + 1)) :=
  Fin.castOrderIso (Nat.add_comm (m + 1) n)

namespace FiniteOrderedTimes

/-- Restrict an ordered family to the coordinates at or before a designated cut. -/
def initialSegment {m n : ℕ}
    (times : FiniteOrderedTimes (n + (m + 1))) : FiniteOrderedTimes (m + 1) :=
  times.restrict ((Fin.castAddOrderEmb n).trans (cutIndexOrderIso m n).toOrderEmbedding)

/-- Times after the cut, measured relative to the time at the cut. -/
def relativeFinalSegment {m n : ℕ}
    (times : FiniteOrderedTimes (n + (m + 1))) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦
      times (cutIndexOrderIso m n (Fin.natAdd (m + 1) i)) -
        times (cutIndexOrderIso m n (Fin.castAdd n (Fin.last m))))
    fun i j hij ↦ by
      have hcut :
          cutIndexOrderIso m n (Fin.castAdd n (Fin.last m)) ≤
            cutIndexOrderIso m n (Fin.natAdd (m + 1) i) := by
        apply (cutIndexOrderIso m n).le_iff_le.mpr
        apply Fin.mk_le_mk.mpr
        change m ≤ m + 1 + i
        omega
      exact tsub_lt_tsub_right_of_le (times.monotone hcut)
        (times.strictMono ((cutIndexOrderIso m n).strictMono
          (Fin.natAddOrderEmb (m + 1) |>.strictMono hij)))

@[simp]
theorem relativeFinalSegment_apply {m n : ℕ}
    (times : FiniteOrderedTimes (n + (m + 1))) (i : Fin n) :
    relativeFinalSegment times i =
      times (cutIndexOrderIso m n (Fin.natAdd (m + 1) i)) -
        times (cutIndexOrderIso m n (Fin.castAdd n (Fin.last m))) :=
  rfl

end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha]

private theorem initialSegment_relativeTail {m n : ℕ}
    (times : FiniteOrderedTimes (n + (m + 2))) :
    FiniteOrderedTimes.initialSegment times.relativeTail =
      (FiniteOrderedTimes.initialSegment times).relativeTail := by
  apply DFunLike.ext _ _
  intro i
  rfl

private theorem relativeFinalSegment_relativeTail {m n : ℕ}
    (times : FiniteOrderedTimes (n + (m + 2))) :
    FiniteOrderedTimes.relativeFinalSegment times.relativeTail =
      FiniteOrderedTimes.relativeFinalSegment times := by
  apply DFunLike.ext _ _
  intro i
  change
    (times _ - times 0) - (times _ - times 0) = times _ - times _
  rw [tsub_tsub_tsub_cancel_right (times.monotone (Fin.zero_le _))]
  apply congrArg₂ (· - ·)
  · apply congrArg times
    apply Fin.ext
    simp [cutIndexOrderIso]
    omega
  · apply congrArg times
    apply Fin.ext
    simp [cutIndexOrderIso]

/-- Separate a finite path into its coordinates at or before the cut and those after the cut. -/
def splitFinitePath {m n : ℕ} (path : Fin (n + (m + 1)) → alpha) :
    (Fin (m + 1) → alpha) × (Fin n → alpha) :=
  (fun i ↦ path (cutIndexOrderIso m n (Fin.castAdd n i)),
    fun i ↦ path (cutIndexOrderIso m n (Fin.natAdd (m + 1) i)))

/-- Splitting a finite path at a cut is measurable. -/
theorem measurable_splitFinitePath {m n : ℕ} :
    Measurable (splitFinitePath (alpha := alpha) (m := m) (n := n)) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply
      (cutIndexOrderIso m n (Fin.castAdd n i))
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply
      (cutIndexOrderIso m n (Fin.natAdd (m + 1) i))

omit [MeasurableSpace alpha] in
private theorem splitFinitePath_cons {m n : ℕ}
    (z : alpha × (Fin (n + (m + 1)) → alpha)) :
    splitFinitePath (m := m + 1) (n := n) (Fin.cons z.1 z.2) =
      (Fin.cons z.1 (splitFinitePath (m := m) (n := n) z.2).1,
        (splitFinitePath (m := m) (n := n) z.2).2) := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp only [splitFinitePath]
      have hidx :
          cutIndexOrderIso (m + 1) n (Fin.castAdd n j.succ) =
            (cutIndexOrderIso m n (Fin.castAdd n j)).succ := by
        apply Fin.ext
        simp [cutIndexOrderIso]
      rw [hidx, Fin.cons_succ, Fin.cons_succ]
  · funext i
    simp only [splitFinitePath]
    have hidx :
        cutIndexOrderIso (m + 1) n (Fin.natAdd (m + 1 + 1) i) =
          (cutIndexOrderIso m n (Fin.natAdd (m + 1) i)).succ := by
      apply Fin.ext
      simp [cutIndexOrderIso]
      omega
    rw [hidx, Fin.cons_succ]

/-- The terminal state of the first component of a split finite path. -/
def splitPastTerminal {m : ℕ}
    (z : alpha × (Fin (m + 1) → alpha)) : alpha :=
  z.2 (Fin.last m)

/-- Reading the terminal past coordinate is measurable. -/
theorem measurable_splitPastTerminal {m : ℕ} :
    Measurable (splitPastTerminal (alpha := alpha) (m := m)) :=
  (measurable_pi_apply (Fin.last m)).comp measurable_snd

/-- Measurable equivalence between a head/tail pair and a finite successor path. -/
def finConsMeasurableEquiv (n : ℕ) :
    alpha × (Fin n → alpha) ≃ᵐ (Fin (n + 1) → alpha) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ alpha) 0).symm

@[simp]
theorem finConsMeasurableEquiv_apply (n : ℕ) (z : alpha × (Fin n → alpha)) :
    finConsMeasurableEquiv n z = Fin.cons z.1 z.2 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

@[simp]
theorem finConsMeasurableEquiv_symm_apply (n : ℕ) (path : Fin (n + 1) → alpha) :
    (finConsMeasurableEquiv n).symm path = (path 0, Fin.tail path) := by
  rfl

private theorem measurable_headTail {n : ℕ} :
    Measurable (fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path)) := by
  apply Measurable.prodMk (measurable_pi_apply 0)
  exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply i.succ

omit [MeasurableSpace alpha] in
private theorem headTail_finCons {n : ℕ} (z : alpha × (Fin n → alpha)) :
    ((fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path))
      (@Fin.cons n (fun _ ↦ alpha) z.1 z.2)) = z := by
  apply Prod.ext
  · rfl
  · funext i
    rfl

private theorem compProd_map_left_equiv
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (kappa : Kernel X A) [IsSFiniteKernel kappa]
    (eta : Kernel (X × A) B) [IsSFiniteKernel eta]
    (E : A ≃ᵐ C) :
    (kappa ⊗ₖ eta).map (Prod.map E id) =
      kappa.map E ⊗ₖ eta.comap
        (fun z : X × C ↦ (z.1, E.symm z.2))
        (measurable_fst.prodMk (E.symm.measurable.comp measurable_snd)) := by
  ext x s hs
  rw [Kernel.map_apply' _ (E.measurable.prodMap measurable_id) x hs,
    Kernel.compProd_apply (hs.preimage (E.measurable.prodMap measurable_id)),
    Kernel.compProd_apply hs]
  rw [Kernel.map_apply kappa E.measurable x]
  rw [MeasureTheory.lintegral_map]
  · congr with a
    rw [Kernel.comap_apply]
    change eta (x, a) (Prod.mk (E a) ⁻¹' s) = _
    rw [E.symm_apply_apply]
  · exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left' hs x
  · exact E.measurable

private theorem map_compProd_prodMkLeft_right
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (kappa : Kernel X A) [IsSFiniteKernel kappa]
    (eta : Kernel A B) [IsSFiniteKernel eta]
    (f : B → C) (hf : Measurable f) :
    (kappa ⊗ₖ Kernel.prodMkLeft X eta).map
        (fun z ↦ (z.1, f z.2)) =
      kappa ⊗ₖ Kernel.prodMkLeft X (eta.map f) := by
  have hpair : Measurable (fun z : A × B ↦ (z.1, f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  congr with a
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
    Kernel.map_apply' _ hf _ (measurable_prodMk_left hs)]
  rfl

private theorem compProd_prodMkLeft_assoc
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (kappa : Kernel X A) 
    (eta : Kernel A B) [IsSFiniteKernel eta]
    (xi : Kernel (A × B) C) [IsSFiniteKernel xi] :
    (kappa ⊗ₖ Kernel.prodMkLeft X (eta ⊗ₖ xi)).map
        MeasurableEquiv.prodAssoc.symm =
      (kappa ⊗ₖ Kernel.prodMkLeft X eta) ⊗ₖ
        xi.comap (fun z : X × (A × B) ↦ z.2)
          measurable_snd := by
  let xiLift : Kernel (X × (A × B)) C :=
    xi.comap (fun z : X × (A × B) ↦ z.2) measurable_snd
  have hinner :
      Kernel.prodMkLeft X (eta ⊗ₖ xi) =
        Kernel.prodMkLeft X eta ⊗ₖ
          xiLift.comap MeasurableEquiv.prodAssoc
            MeasurableEquiv.prodAssoc.measurable := by
    ext z s hs
    rw [Kernel.prodMkLeft_apply', Kernel.compProd_apply hs]
    rw [Kernel.compProd_apply hs]
    congr with b
  rw [hinner]
  simpa only [xiLift] using
    (Kernel.compProd_assoc (κ := kappa) (η := Kernel.prodMkLeft X eta)
      (ξ := xiLift))

/-- Splitting the finite-time kernel after its first observation recovers exactly the recursive
transition-kernel product used in its construction. -/
theorem finiteTimeKernel_map_headTail (P : SubMarkovKernelSemigroup alpha) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    (finiteTimeKernel P times).map
        (fun path ↦ (path 0, Fin.tail path)) =
      P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
        (finiteTimeKernel P times.relativeTail) := by
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
  · have hcomp :
        (fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path)) ∘
            (fun z : alpha × (Fin n → alpha) ↦
              @Fin.cons n (fun _ ↦ alpha) z.1 z.2) = id := by
          funext z
          exact headTail_finCons z
    rw [hcomp, Kernel.map_id]
  · exact measurable_pi_iff.mpr fun i ↦ Fin.cases measurable_fst
      (fun j ↦ (measurable_pi_apply j).comp measurable_snd) i
  · exact measurable_headTail

private theorem finiteTimeKernel_one_eq_map (P : SubMarkovKernelSemigroup alpha)
    (times : FiniteOrderedTimes 1) :
    finiteTimeKernel P times =
      (P (times 0)).map (fun x ↦ fun _ : Fin 1 ↦ x) := by
  calc
    finiteTimeKernel P times =
        ((finiteTimeKernel P times).map (fun path ↦ path 0)).map
          (fun x ↦ fun _ : Fin 1 ↦ x) := by
      rw [← Kernel.map_comp_right]
      · have hcomp :
            (fun x : alpha ↦ fun _ : Fin 1 ↦ x) ∘
                (fun path : Fin 1 → alpha ↦ path 0) = id := by
              funext path
              funext i
              exact Fin.eq_zero i ▸ rfl
        rw [hcomp, Kernel.map_id]
      · exact measurable_pi_apply 0
      · exact measurable_pi_iff.mpr fun _ ↦ measurable_id
    _ = (P (times 0)).map (fun x ↦ fun _ : Fin 1 ↦ x) := by
      rw [finiteTimeKernel_one_map_eval]

namespace IsConservative

private theorem finiteTimeKernel_map_splitFinitePath_zero
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (n : ℕ) (times : FiniteOrderedTimes (n + 1)) :
    (finiteTimeKernel P times).map
        (splitFinitePath (alpha := alpha) (m := 0) (n := n)) =
      finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := 0))
          measurable_splitPastTerminal := by
  let E : alpha ≃ᵐ (Fin 1 → alpha) :=
    (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ alpha)).symm
  have hE (x : alpha) : E x = fun _ : Fin 1 ↦ x := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hfuture :
      FiniteOrderedTimes.relativeFinalSegment times = times.relativeTail := by
    apply DFunLike.ext _ _
    intro i
    change times _ - times _ = times _ - times _
    apply congrArg₂ (· - ·) <;> apply congrArg times <;> apply Fin.ext <;>
      simp [cutIndexOrderIso]
  have hsplit :
      splitFinitePath (alpha := alpha) (m := 0) (n := n) =
        Prod.map E id ∘
          (fun path : Fin (n + 1) → alpha ↦ (path 0, Fin.tail path)) := by
    funext path
    apply Prod.ext
    · funext i
      change path _ = E (path 0) i
      rw [hE]
      have hi : i = 0 := Fin.eq_zero i
      subst i
      congr 1
    · funext i
      change path _ = path i.succ
      congr 1
      apply Fin.ext
      simp [cutIndexOrderIso]
  let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
    hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
  let : IsMarkovKernel (P (times 0)) := hP.isMarkovKernel (times 0)
  rw [hsplit, Kernel.map_comp_right _ measurable_headTail
    (E.measurable.prodMap measurable_id), finiteTimeKernel_map_headTail]
  rw [compProd_map_left_equiv]
  rw [finiteTimeKernel_one_eq_map, hfuture]
  congr 1

/-- Splitting an ordered finite-dimensional law at a cut factors it into its past law and the
relative future law started from the terminal state of that past. -/
theorem finiteTimeKernel_map_splitFinitePath
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (m n : ℕ) (times : FiniteOrderedTimes (n + (m + 1))) :
    (finiteTimeKernel P times).map
        (splitFinitePath (alpha := alpha) (m := m) (n := n)) =
      finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := m))
          measurable_splitPastTerminal := by
  induction m with
  | zero => exact finiteTimeKernel_map_splitFinitePath_zero P hP n times
  | succ m ih =>
      let E := finConsMeasurableEquiv (alpha := alpha) (m + 1)
      let g : alpha × ((Fin (m + 1) → alpha) × (Fin n → alpha)) →
          (Fin (m + 2) → alpha) × (Fin n → alpha) :=
        fun z ↦ (Fin.cons z.1 z.2.1, z.2.2)
      have hg : Measurable g := by
        apply Measurable.prodMk
        · rw [measurable_pi_iff]
          intro i
          refine Fin.cases measurable_fst (fun j ↦ ?_) i
          exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
        · exact measurable_snd.comp measurable_snd
      let f : alpha × (Fin (n + (m + 1)) → alpha) →
          alpha × ((Fin (m + 1) → alpha) × (Fin n → alpha)) :=
        fun z ↦ (z.1, splitFinitePath (m := m) (n := n) z.2)
      have hf : Measurable f :=
        measurable_fst.prodMk (measurable_splitFinitePath.comp measurable_snd)
      have hcomp :
          splitFinitePath (alpha := alpha) (m := m + 1) (n := n) ∘
              (fun z : alpha × (Fin (n + (m + 1)) → alpha) ↦
                Fin.cons z.1 z.2) =
            g ∘ f := by
        funext z
        exact splitFinitePath_cons z
      let : IsMarkovKernel (P (times 0)) := hP.isMarkovKernel (times 0)
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
      let : IsMarkovKernel
          (finiteTimeKernel P (FiniteOrderedTimes.initialSegment times.relativeTail)) :=
        hP.isMarkovKernel_finiteTimeKernel P _
      let : IsMarkovKernel
          (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times.relativeTail)) :=
        hP.isMarkovKernel_finiteTimeKernel P _
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        ← Kernel.map_comp_right]
      · refine (congrArg (fun f ↦
            (P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
              (finiteTimeKernel P times.relativeTail)).map f) hcomp).trans ?_
        rw [Kernel.map_comp_right _ hf hg]
        have hsplitMap :
            (P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
                (finiteTimeKernel P times.relativeTail)).map f =
              P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
                ((finiteTimeKernel P times.relativeTail).map
                  (splitFinitePath (alpha := alpha) (m := m) (n := n))) := by
          simpa only [f] using! map_compProd_prodMkLeft_right
            (P (times 0)) (finiteTimeKernel P times.relativeTail)
            (splitFinitePath (alpha := alpha) (m := m) (n := n))
            measurable_splitFinitePath
        refine (congrArg (fun K ↦ K.map g) hsplitMap).trans ?_
        rw [ih times.relativeTail]
        have hg_assoc : g = Prod.map E id ∘ MeasurableEquiv.prodAssoc.symm := by
          funext z
          apply Prod.ext
          · funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
          · rfl
        rw [hg_assoc, Kernel.map_comp_right _
          MeasurableEquiv.prodAssoc.symm.measurable
          (E.measurable.prodMap measurable_id)]
        rw [compProd_prodMkLeft_assoc]
        rw [compProd_map_left_equiv]
        rw [initialSegment_relativeTail, relativeFinalSegment_relativeTail]
        congr 1
        have hEfun : (E : alpha × (Fin (m + 1) → alpha) →
            Fin (m + 2) → alpha) = fun z ↦ Fin.cons z.1 z.2 := by
          funext z i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
        rw [hEfun, ← Kernel.mapOfMeasurable_eq_map]
        exact (finiteTimeKernel_succ P
          (FiniteOrderedTimes.initialSegment times)).symm
      · exact measurable_pi_iff.mpr fun i ↦ Fin.cases measurable_fst
          (fun j ↦ (measurable_pi_apply j).comp measurable_snd) i
      · exact measurable_splitFinitePath


end IsConservative

end SubMarkovKernelSemigroup
end MarkovProcess
