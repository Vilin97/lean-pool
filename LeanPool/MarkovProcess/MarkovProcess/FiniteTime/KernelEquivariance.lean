/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.ProjectiveFamily
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KolmogorovMoments
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic


/-!
# Rescaled conjugation of finite-time kernels

A sub-Markov kernel semigroup `P'` on a state space `beta` is the *rescaled conjugate* of `P` on
`alpha` when it is obtained from `P` by conjugating the state with a homeomorphism `e : alpha ≃ₜ
    beta`
and speeding time up by a positive factor `c`, that is `P' t x = ((P (c * t)) (e.symm x)).map e`.

This file transfers the finite-dimensional laws across such a relation.  The main result is
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq`, which computes every
finite-time kernel of `P'` from the finite-time kernel of `P` at the rescaled times.  Supporting
API: the time-scaling operation `FiniteOrderedTimes.rescale`, the coordinatewise state map
`FiniteOrderedTimes.mapPath`, and two composition-product lemmas, `comap_compProd_prodMkLeft` and
`map_compProd_prodMkLeft_conjugate`, which have no direct Mathlib counterpart.

Nothing here mentions path space; the path-space equivariance statement is in
`MarkovProcess/Trajectory/Equivariance.lean`.  When the state map is an isometry, the intrinsic
Kolmogorov moment criterion also transfers, with the constant multiplied by `c ^ q`
(`IsRescaledConjugate.hasKolmogorovMoments`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MarkovProcess

namespace FiniteOrderedTimes

/-- Multiply every time of a finite ordered family by a fixed positive factor.  Positivity of the
factor is what keeps the family strictly increasing. -/
def rescale {n : ℕ} (c : NNReal) (hc : 0 < c) (times : FiniteOrderedTimes n) :
    FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ c * times i) fun _ _ hij ↦
    mul_lt_mul_of_pos_left (times.strictMono hij) hc

/-- Rescaled times, evaluated. -/
@[simp]
theorem rescale_apply {n : ℕ} (c : NNReal) (hc : 0 < c) (times : FiniteOrderedTimes n)
    (i : Fin n) : times.rescale c hc i = c * times i :=
  rfl

/-- Rescaling by the factor one does not change a finite ordered time family. -/
@[simp]
theorem rescale_one {n : ℕ} (times : FiniteOrderedTimes n) :
    times.rescale 1 one_pos = times := by
  apply DFunLike.ext _ _
  intro i
  exact one_mul (times i)

/-- Successive rescalings combine by multiplication. -/
theorem rescale_rescale {n : ℕ} (c d : NNReal) (hc : 0 < c) (hd : 0 < d)
    (times : FiniteOrderedTimes n) :
    (times.rescale d hd).rescale c hc = times.rescale (c * d) (mul_pos hc hd) := by
  apply DFunLike.ext _ _
  intro i
  exact (mul_assoc c d (times i)).symm

/-- Rescaling commutes with passing to the relative tail: subtracting the first time and then
scaling is the same as scaling and then subtracting the scaled first time. -/
@[simp]
theorem relativeTail_rescale {n : ℕ} (c : NNReal) (hc : 0 < c)
    (times : FiniteOrderedTimes (n + 1)) :
    (times.rescale c hc).relativeTail = times.relativeTail.rescale c hc := by
  apply DFunLike.ext _ _
  intro i
  simp only [relativeTail_apply, rescale_apply]
  exact (mul_tsub c (times i.succ) (times 0)).symm

/-- Apply a map of the state space to every coordinate of a coordinate path. -/
def mapPath {ι alpha beta : Type*} (e : alpha → beta) (path : ι → alpha) : ι → beta :=
  fun i ↦ e (path i)

/-- A path mapped coordinatewise, evaluated. -/
@[simp]
theorem mapPath_apply {ι alpha beta : Type*} (e : alpha → beta) (path : ι → alpha) (i : ι) :
    mapPath e path i = e (path i) :=
  rfl

/-- The coordinatewise state map is measurable when the state map is. -/
theorem measurable_mapPath {ι alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {e : alpha → beta} (he : Measurable e) :
    Measurable (mapPath e : (ι → alpha) → ι → beta) :=
  measurable_pi_iff.mpr fun i ↦ he.comp (measurable_pi_apply i)

/-- The coordinatewise state map commutes with restriction along an embedding of index sets. -/
theorem mapPath_comp_restrictPath {m n : ℕ} (d : Fin m ↪o Fin n) {alpha beta : Type*}
    (e : alpha → beta) :
    mapPath e ∘ (restrictPath d : (Fin n → alpha) → Fin m → alpha) =
      restrictPath d ∘ mapPath e :=
  rfl

/-- Prepending a state to a finite path commutes with the coordinatewise state map. -/
theorem mapPath_finCons {n : ℕ} {alpha beta : Type*} (e : alpha → beta)
    (z : alpha × (Fin n → alpha)) :
    mapPath e (@Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1 z.2) =
      @Fin.cons n (fun _ : Fin (n + 1) ↦ beta) (e z.1) (mapPath e z.2) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup

/-- The increasing enumeration of a finite set of times, read at the position of one of its
elements, returns that element. -/
theorem finiteSetTimes_orderIsoOfFin_symm_apply (I : Finset NNReal) (t : I) :
    finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = (t : NNReal) := by
  change I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm t) = (t : NNReal)
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

section CompProd

variable {X X' Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']

/-- Pulling the source of a composition-product back along a measurable map only affects the first
factor, because a `prodMkLeft` second factor does not read the source. -/
theorem comap_compProd_prodMkLeft (kappa : Kernel X Y) [IsSFiniteKernel kappa]
    (eta : Kernel Y Z) [IsSFiniteKernel eta] {g : X' → X} (hg : Measurable g) :
    Kernel.comap (kappa ⊗ₖ Kernel.prodMkLeft X eta) g hg =
      (Kernel.comap kappa g hg) ⊗ₖ Kernel.prodMkLeft X' eta := by
  ext x s hs
  rw [Kernel.comap_apply', Kernel.compProd_apply hs, Kernel.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply, Kernel.comap_apply]

/-- Relabelling a composition-product coordinatewise.  Relabelling the first coordinate by an
invertible measurable map `f` and the second by a measurable map `g` gives the composition-product
of the relabelled factors, the second factor being read at the `f`-preimage of its new index. -/
theorem map_compProd_prodMkLeft_conjugate (kappa : Kernel X Y) [IsSFiniteKernel kappa]
    (eta : Kernel Y Z) [IsSFiniteKernel eta] {f : Y → Y'} {f' : Y' → Y}
    (hf : Measurable f) (hf' : Measurable f') (hleft : Function.LeftInverse f' f)
    (hright : Function.RightInverse f' f) {g : Z → Z'} (hg : Measurable g) :
    (kappa ⊗ₖ Kernel.prodMkLeft X eta).map (fun z ↦ (f z.1, g z.2)) =
      (kappa.map f) ⊗ₖ Kernel.prodMkLeft X ((Kernel.comap eta f' hf').map g) := by
  set F : Y ≃ᵐ Y' :=
    { toEquiv := ⟨f, f', hleft, hright⟩
      measurable_toFun := hf
      measurable_invFun := hf' } with hF
  have hpair : Measurable (fun z : Y × Z ↦ (f z.1, g z.2)) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs, Kernel.compProd_apply (hs.preimage hpair),
    Kernel.compProd_apply hs, Kernel.map_apply _ hf,
    show (kappa x).map f = (kappa x).map (F : Y → Y') from rfl,
    MeasureTheory.lintegral_map_equiv _ F]
  refine lintegral_congr fun y ↦ ?_
  have hsection : MeasurableSet (Prod.mk (f y) ⁻¹' s) := measurable_prodMk_left hs
  change eta y (Prod.mk y ⁻¹' ((fun z : Y × Z ↦ (f z.1, g z.2)) ⁻¹' s)) =
      ((Kernel.comap eta f' hf').map g) (f y) (Prod.mk (f y) ⁻¹' s)
  rw [Kernel.map_apply' _ hg _ hsection, Kernel.comap_apply, hleft y]
  rfl

end CompProd

section RescaledConjugate

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]

/-- `P'` is the *rescaled conjugate* of `P` by the homeomorphism `e` and the time factor `c`:
started at `x`, the state of `P'` at time `t` is the image under `e` of the state of `P` at the
sped-up time `c * t` started at `e.symm x`. -/
def IsRescaledConjugate (P : SubMarkovKernelSemigroup alpha) (P' : SubMarkovKernelSemigroup beta)
    (e : alpha ≃ₜ beta)
    (c : NNReal) : Prop :=
  ∀ t x, P' t x = ((P (c * t)) (e.symm x)).map e

namespace IsRescaledConjugate

variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ
    beta}
  {c : NNReal}

/-- The rescaled-conjugacy relation in kernel form: at every time the transition kernel of `P'` is
the transition kernel of `P` at the sped-up time, conjugated by `e`. -/
theorem kernel_eq (h : IsRescaledConjugate P P' e c) (t : NNReal) :
    P' t = (Kernel.comap (P (c * t)) e.symm e.symm.measurable).map e := by
  refine Kernel.ext fun x ↦ ?_
  rw [Kernel.map_apply _ e.measurable, Kernel.comap_apply]
  exact h t x

/-- Conservativity transfers across rescaled conjugacy: no mass is lost by conjugating with a
homeomorphism and speeding up time. -/
theorem isConservative (h : IsRescaledConjugate P P' e c) (hP : P.IsConservative) :
    P'.IsConservative := by
  intro t x
  rw [h t x, Measure.map_apply e.measurable MeasurableSet.univ, Set.preimage_univ]
  exact hP (c * t) (e.symm x)

/-- **Finite-dimensional transfer.**  Every finite-time kernel of the rescaled conjugate `P'` is
the finite-time kernel of `P` at the rescaled times, started from the `e`-preimage of the initial
state and read through `e` in every coordinate. -/
theorem finiteTimeKernel_eq (h : IsRescaledConjugate P P' e c) (hc : 0 < c)
    (hP : P.IsConservative) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n),
      finiteTimeKernel P' times =
        (Kernel.comap (finiteTimeKernel P (times.rescale c hc)) e.symm
          e.symm.measurable).map (FiniteOrderedTimes.mapPath e) := by
  intro n
  induction n with
  | zero =>
      intro times
      refine Kernel.ext fun x ↦ ?_
      simp only [finiteTimeKernel_zero]
      rw [Kernel.map_apply _ (FiniteOrderedTimes.measurable_mapPath (ι := Fin 0) e.measurable),
        Kernel.comap_apply, Kernel.const_apply, Kernel.const_apply,
        Measure.map_dirac (FiniteOrderedTimes.emptyPath alpha)]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro times
      let : IsFiniteKernel (P (c * times 0)) :=
        (P.isSubMarkovKernel (c * times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P (times.relativeTail.rescale c hc)) :=
        hP.isMarkovKernel_finiteTimeKernel P (times.relativeTail.rescale c hc)
      have hmapn : Measurable
          (FiniteOrderedTimes.mapPath e : (Fin n → alpha) → Fin n → beta) :=
        FiniteOrderedTimes.measurable_mapPath e.measurable
      have hconj : Measurable (fun z : alpha × (Fin n → alpha) ↦
          (e z.1, FiniteOrderedTimes.mapPath e z.2)) :=
        (e.measurable.comp measurable_fst).prodMk (hmapn.comp measurable_snd)
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, FiniteOrderedTimes.relativeTail_rescale,
        FiniteOrderedTimes.rescale_apply,
        Kernel.comap_map_comm _ e.symm.measurable measurable_finCons,
        ← Kernel.map_comp_right _ measurable_finCons
          (FiniteOrderedTimes.measurable_mapPath (ι := Fin (n + 1)) e.measurable),
        show (FiniteOrderedTimes.mapPath e ∘ fun z : alpha × (Fin n → alpha) ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1 z.2) =
            (fun z : beta × (Fin n → beta) ↦
                @Fin.cons n (fun _ : Fin (n + 1) ↦ beta) z.1 z.2) ∘
              (fun z : alpha × (Fin n → alpha) ↦ (e z.1, FiniteOrderedTimes.mapPath e z.2)) from
          funext fun z ↦ FiniteOrderedTimes.mapPath_finCons e z,
        Kernel.map_comp_right _ hconj (measurable_finCons (α := beta)),
        comap_compProd_prodMkLeft _ _ e.symm.measurable,
        map_compProd_prodMkLeft_conjugate _ _ e.measurable e.symm.measurable
          e.symm_apply_apply e.apply_symm_apply hmapn,
        ← h.kernel_eq (times 0), ← ih times.relativeTail]

/-- **Finite-set transfer.**  The finite-dimensional law of the rescaled conjugate `P'` on a
finite set `I` of times is the law of `P` at the times `c * t`, `t ∈ I`, started from the
`e`-preimage of the initial state and read through `e` in every coordinate. -/
theorem finiteSetKernel_eq (h : IsRescaledConjugate P P' e c) (hc : 0 < c)
    (hP : P.IsConservative) (I : Finset NNReal) :
    finiteSetKernel P' I =
      (Kernel.comap (finiteTimeKernel P ((finiteSetTimes I).rescale c hc)) e.symm
          e.symm.measurable).map
        (FiniteOrderedTimes.mapPath e ∘ orderedPathToFiniteSet I) := by
  have hmap : Measurable
      (FiniteOrderedTimes.mapPath e : (Fin I.card → alpha) → Fin I.card → beta) :=
    FiniteOrderedTimes.measurable_mapPath e.measurable
  rw [finiteSetKernel_eq_map, h.finiteTimeKernel_eq hc hP (finiteSetTimes I),
    ← Kernel.map_comp_right _ hmap (measurable_orderedPathToFiniteSet I),
    show (orderedPathToFiniteSet (α := beta) I ∘ FiniteOrderedTimes.mapPath e) =
        FiniteOrderedTimes.mapPath e ∘ orderedPathToFiniteSet I from rfl]

end IsRescaledConjugate

section Moments

variable {alpha beta : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [PseudoEMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]
variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ
    beta}
  {c : NNReal}

/-- **Transfer of the Kolmogorov moment criterion.**  If the state map `e` is an isometry, then
the intrinsic displacement bound of `P` passes to its rescaled conjugate `P'` with the constant
multiplied by `c ^ q`: the conjugation leaves the displacement untouched and speeding time up by
`c` multiplies the time budget `h ^ q` by `c ^ q`. -/
theorem IsRescaledConjugate.hasKolmogorovMoments
    (h : IsRescaledConjugate P P' e c) (he : Isometry (e : alpha → beta)) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P'.HasKolmogorovMoments p q (M * c ^ q) := by
  obtain ⟨hp, hq, hbound⟩ := hmom
  have hq0 : (0 : ℝ) ≤ q := le_of_lt (lt_trans zero_lt_one hq)
  refine ⟨hp, hq, fun t y ↦ ?_⟩
  have hstep : ∫⁻ z, edist z y ^ p ∂(P' t y) =
      ∫⁻ w, edist w (e.symm y) ^ p ∂(P (c * t) (e.symm y)) := by
    have hmeas : Measurable (fun z : beta ↦ edist z y ^ p) :=
      (measurable_edist_left (x := y)).pow_const p
    rw [h t y, MeasureTheory.lintegral_map hmeas e.measurable]
    refine lintegral_congr fun w ↦ ?_
    congr 1
    conv_lhs => rw [← e.apply_symm_apply y]
    exact he.edist_eq w (e.symm y)
  rw [hstep]
  refine le_trans (hbound (c * t) (e.symm y)) (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.mul_rpow_of_nonneg _ _ hq0, ← mul_assoc, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg c hq0]

end Moments

end RescaledConjugate

end SubMarkovKernelSemigroup

end MarkovProcess
