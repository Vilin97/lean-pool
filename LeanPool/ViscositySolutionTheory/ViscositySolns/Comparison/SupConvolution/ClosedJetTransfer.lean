/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.SupConvolution.SuperjetTransfer

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Sup-convolution declarations (ClosedJetTransfer)

Part of the compact-set sup-convolution development used in the appendix
proof of the maximum principle for semicontinuous functions. Split from
`SupConvolution.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
The value component of the graph map used in the closed-superjet transfer.

If `r` is the sup-convolution value at `ξ` and
`y = supConvolutionTransferPoint lambda ξ J`, then the corresponding value
of the original function is expected to be

`r + (lambda / 2) * ∑ i, (y i - ξ i)^2`.
-/
def supConvolutionTransferValue (lambda : Real) (ξ : Point n) (r : Real) (J : Jet n) :
    Real :=
  r + (lambda / 2) *
    dotProduct (supConvolutionTransferPoint lambda ξ J - ξ)
      (supConvolutionTransferPoint lambda ξ J - ξ)

/--
The graph map used to pass from closed superjets of a compact sup-convolution
to closed superjets of the original function.
-/
def supConvolutionTransferGraphPoint (lambda : Real)
    (z : (Point n × Real) × Jet n) : (Point n × Real) × Jet n :=
  let y := supConvolutionTransferPoint lambda z.1.1 z.2
  ((y, supConvolutionTransferValue lambda z.1.1 z.1.2 z.2), z.2)

/-- The sup-convolution graph-transfer map is continuous. -/
theorem continuous_supConvolutionTransferGraphPoint (lambda : Real) :
    Continuous (fun z : (Point n × Real) × Jet n =>
      supConvolutionTransferGraphPoint (n := n) lambda z) := by
  let xi : ((Point n × Real) × Jet n) -> Point n := fun z => z.1.1
  let r : ((Point n × Real) × Jet n) -> Real := fun z => z.1.2
  let J : ((Point n × Real) × Jet n) -> Jet n := fun z => z.2
  let y : ((Point n × Real) × Jet n) -> Point n :=
    fun z => xi z + lambda⁻¹ • (J z).gradient
  have hxi : Continuous xi := continuous_fst.comp continuous_fst
  have hr : Continuous r := continuous_snd.comp continuous_fst
  have hJ : Continuous J := continuous_snd
  have hgrad : Continuous fun z => (J z).gradient := Jet.continuous_gradient.comp hJ
  have hy : Continuous y := by
    dsimp [y]
    exact hxi.add (hgrad.const_smul lambda⁻¹)
  have hvalue : Continuous fun z =>
      supConvolutionTransferValue (n := n) lambda (xi z) (r z) (J z) := by
    dsimp [supConvolutionTransferValue, supConvolutionTransferPoint, y]
    exact hr.add (continuous_const.mul ((hy.sub hxi).dotProduct (hy.sub hxi)))
  have hleft : Continuous fun z => (y z,
      supConvolutionTransferValue (n := n) lambda (xi z) (r z) (J z)) :=
    hy.prodMk hvalue
  have htarget : Continuous fun z => ((y z,
      supConvolutionTransferValue (n := n) lambda (xi z) (r z) (J z)), J z) :=
    hleft.prodMk hJ
  simpa [supConvolutionTransferGraphPoint, supConvolutionTransferPoint,
    supConvolutionTransferValue, xi, r, J, y] using htarget

/--
At a closure point of the superjet graph of an upper semicontinuous function,
the limiting value is bounded above by the function value at the limiting
base point.

In quantified mathematical form, if `K` is closed, `v` is upper
semicontinuous on `K`, and `((x, r), J)` belongs to the closure of
`SuperjetGraph K v`, then `x ∈ K` and `r ≤ v x`.
-/
theorem mem_closure_superjetGraph_value_le_of_upperSemicontinuousOn
    {K : Set (Point n)} {v : Point n -> Real}
    {z : (Point n × Real) × Jet n}
    (hKclosed : IsClosed K) (hv : UpperSemicontinuousOn v K)
    (hz : z ∈ closure (SuperjetGraph K v)) :
    z.1.1 ∈ K ∧ z.1.2 <= v z.1.1 := by
  let H : Set ((Point n × Real) × Jet n) :=
    {z | z.1.1 ∈ K ∧ z.1.2 <= v z.1.1}
  have hHclosed : IsClosed H := by
    have hhyp : IsClosed {p : Point n × Real | p.1 ∈ K ∧ p.2 <= v p.1} :=
      (upperSemicontinuousOn_iff_isClosed_hypograph hKclosed).1 hv
    change IsClosed ((fun z : (Point n × Real) × Jet n => z.1) ⁻¹'
      {p : Point n × Real | p.1 ∈ K ∧ p.2 <= v p.1})
    exact hhyp.preimage continuous_fst
  have hsubset : SuperjetGraph K v ⊆ H := by
    intro z hz
    rcases z with ⟨⟨x, r⟩, J⟩
    rcases hz with ⟨hxK, hr, _hJ⟩
    change x ∈ K at hxK
    change r = v x at hr
    exact ⟨hxK, by simp [hr]⟩
  exact closure_minimal hsubset hHclosed hz

/--
The value identity for a transfer graph point lying in the closure of the
superjet graph of the original function.

In quantified mathematical form, suppose `K` is nonempty and compact, `v` is
upper semicontinuous on `K`, and

`supConvolutionTransferGraphPoint lambda ((η, compactSupConvolution lambda K v η), J)`

belongs to the closure of `SuperjetGraph K v`. Then

`v (η + lambda⁻¹ • J.gradient) =
 compactSupConvolution lambda K v η
 + (lambda / 2) * ∑ i, ((η + lambda⁻¹ • J.gradient) i - η i)^2`.
-/
theorem supConvolutionTransferValue_eq_of_mem_closure_superjetGraph_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K)
    (hclosure :
      supConvolutionTransferGraphPoint (n := n) lambda
        ((η, compactSupConvolution lambda K v η), J) ∈
          closure (SuperjetGraph K v)) :
    v (supConvolutionTransferPoint lambda η J) =
      compactSupConvolution lambda K v η +
        (lambda / 2) *
          dotProduct (supConvolutionTransferPoint lambda η J - η)
            (supConvolutionTransferPoint lambda η J - η) := by
  let y : Point n := supConvolutionTransferPoint lambda η J
  let r : Real := supConvolutionTransferValue lambda η (compactSupConvolution lambda K v η) J
  have hupper :
      y ∈ K ∧ r <= v y := by
    have h :=
      mem_closure_superjetGraph_value_le_of_upperSemicontinuousOn
        (K := K) (v := v)
        (z := supConvolutionTransferGraphPoint (n := n) lambda
          ((η, compactSupConvolution lambda K v η), J))
        hKcompact.isClosed hv hclosure
    simpa [supConvolutionTransferGraphPoint, y, r] using h
  rcases hupper with ⟨hyK, hr_le⟩
  have hkernel_le :
      supConvolutionKernel lambda v η y <= compactSupConvolution lambda K v η := by
    refine supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
      (K := K) (u := v) (lambda := lambda) ?_ hyK
    intro ξ
    exact exists_isMaxOn_supConvolutionKernel_of_isCompact hKne hKcompact hv
  have hv_le : v y <= r := by
    dsimp [supConvolutionKernel, supConvolutionTransferValue, y, r] at hkernel_le ⊢
    linarith
  have h_eq : r = v y := le_antisymm hr_le hv_le
  simpa [y, r, supConvolutionTransferValue] using h_eq.symm

/--
Closed-superjet transfer for the compact sup-convolution, stated with explicit
ordinary-graph selection hypotheses.

In quantified mathematical form, suppose that every compact sup-convolution
kernel has a maximum point on `K`. Suppose also that for every ordinary
superjet `(q, Y)` of the compact sup-convolution at `ξ`, the point
`ξ + lambda⁻¹ • q` belongs to `K` and is a maximum point of
`z ↦ v z - (lambda / 2) * ∑ i, (z i - ξ i)^2` on `K`. If `(p, X)` belongs to the
closed superjet of the compact sup-convolution at `η`, and if the value
identity

`v (η + lambda⁻¹ • p) =
 compactSupConvolution lambda K v η
 + (lambda / 2) * ∑ i, ((η + lambda⁻¹ • p) i - η i)^2`

holds, then `(p, X)` belongs to the closed superjet of `v` at
`η + lambda⁻¹ • p` relative to `K`.
-/
theorem closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hmax_exists : ∀ ξ : Point n,
      ∃ z ∈ K, IsMaxOn (fun x : Point n => supConvolutionKernel lambda v ξ x) K z)
    (hselected : ∀ ξ : Point n, ∀ J' : Jet n,
      J' ∈ Superjet Set.univ (fun ζ : Point n => compactSupConvolution lambda K v ζ) ξ ->
        supConvolutionTransferPoint lambda ξ J' ∈ K ∧
          IsMaxOn (fun z : Point n => supConvolutionKernel lambda v ξ z) K
            (supConvolutionTransferPoint lambda ξ J'))
    (hvalue :
      v (supConvolutionTransferPoint lambda η J) =
        compactSupConvolution lambda K v η +
          (lambda / 2) *
            dotProduct (supConvolutionTransferPoint lambda η J - η)
              (supConvolutionTransferPoint lambda η J - η))
    (hJ : J ∈ ClosedSuperjet Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    J ∈ ClosedSuperjet K v (supConvolutionTransferPoint lambda η J) := by
  let vhat : Point n -> Real := fun ξ => compactSupConvolution lambda K v ξ
  let T : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => supConvolutionTransferGraphPoint (n := n) lambda z
  have hTcont : Continuous T := by
    simpa [T] using continuous_supConvolutionTransferGraphPoint (n := n) lambda
  have hT_mem :
      T ((η, vhat η), J) ∈ closure (T '' SuperjetGraph Set.univ vhat) :=
    image_closure_subset_closure_image hTcont ⟨((η, vhat η), J), hJ, rfl⟩
  have hsubset : T '' SuperjetGraph Set.univ vhat ⊆ SuperjetGraph K v := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨ξ, r⟩, J'⟩
    rcases hw with ⟨_hξ, hr, hJ'⟩
    change r = vhat ξ at hr
    subst r
    rcases hselected ξ J' hJ' with ⟨hy, hmax⟩
    have hJv :
        J' ∈ Superjet K v (supConvolutionTransferPoint lambda ξ J') :=
      superjet_of_superjet_compactSupConvolution_of_isMaxOn
        (K := K) (v := v) (lambda := lambda) (η := ξ)
        (y := supConvolutionTransferPoint lambda ξ J')
        hmax_exists hy hmax hJ'
    have hvalue_graph :
        supConvolutionTransferValue lambda ξ (vhat ξ) J' =
          v (supConvolutionTransferPoint lambda ξ J') := by
      have heq := compactSupConvolution_eq_of_isMaxOn
        (K := K) (u := v) (lambda := lambda) (ξ := ξ)
        (y := supConvolutionTransferPoint lambda ξ J') hy hmax
      change vhat ξ = supConvolutionKernel lambda v ξ
        (supConvolutionTransferPoint lambda ξ J') at heq
      dsimp [supConvolutionTransferValue]
      rw [heq]
      dsimp [supConvolutionKernel]
      ring
    exact ⟨hy, hvalue_graph, hJv⟩
  have hclosure : T ((η, vhat η), J) ∈ closure (SuperjetGraph K v) :=
    closure_mono hsubset hT_mem
  have hT_target :
      T ((η, vhat η), J) =
        ((supConvolutionTransferPoint lambda η J,
          v (supConvolutionTransferPoint lambda η J)), J) := by
    dsimp [T, supConvolutionTransferGraphPoint, supConvolutionTransferValue, vhat]
    rw [hvalue]
  change ((supConvolutionTransferPoint lambda η J,
    v (supConvolutionTransferPoint lambda η J)), J) ∈ closure (SuperjetGraph K v)
  simpa only [hT_target] using hclosure

/--
Compactness and upper semicontinuity supply the kernel maximum points required
by the closed-superjet transfer theorem.

In quantified mathematical form, let `K` be nonempty and compact, and let `v`
be upper semicontinuous on `K`. Suppose that for every ordinary superjet
`(q, Y)` of the compact sup-convolution at `ξ`, the point `ξ + lambda⁻¹ • q`
belongs to `K` and is a maximum point on `K` of
`z ↦ v z - (lambda / 2) * ∑ i, (z i - ξ i)^2`. If `(p, X)` belongs to the closed
superjet of the compact sup-convolution at `η`, and if the corresponding
value identity holds at `η + lambda⁻¹ • p`, then `(p, X)` belongs to the
closed superjet of `v` at that point relative to `K`.
-/
theorem closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K)
    (hselected : ∀ ξ : Point n, ∀ J' : Jet n,
      J' ∈ Superjet Set.univ (fun ζ : Point n => compactSupConvolution lambda K v ζ) ξ ->
        supConvolutionTransferPoint lambda ξ J' ∈ K ∧
          IsMaxOn (fun z : Point n => supConvolutionKernel lambda v ξ z) K
            (supConvolutionTransferPoint lambda ξ J'))
    (hvalue :
      v (supConvolutionTransferPoint lambda η J) =
        compactSupConvolution lambda K v η +
          (lambda / 2) *
            dotProduct (supConvolutionTransferPoint lambda η J - η)
              (supConvolutionTransferPoint lambda η J - η))
    (hJ : J ∈ ClosedSuperjet Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    J ∈ ClosedSuperjet K v (supConvolutionTransferPoint lambda η J) := by
  refine closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer
    (K := K) (v := v) (lambda := lambda) (η := η) (J := J)
    ?_ hselected hvalue hJ
  intro ξ
  exact exists_isMaxOn_supConvolutionKernel_of_isCompact hKne hKcompact hv

/--
Closed-superjet transfer for compact sup-convolutions, with the ordinary
superjet maximum-point hypothesis discharged by the gradient identity.

In quantified mathematical form, let `K` be nonempty and compact, let `v` be
upper semicontinuous on `K`, and let `lambda ≠ 0`. If `(p, X)` belongs to the
closed superjet of `ξ ↦ compactSupConvolution lambda K v ξ` at `η`, and if

`v (η + lambda⁻¹ • p) =
 compactSupConvolution lambda K v η
 + (lambda / 2) * ∑ i, ((η + lambda⁻¹ • p) i - η i)^2`,

then `(p, X)` belongs to the closed superjet of `v` at
`η + lambda⁻¹ • p` relative to `K`.
-/
theorem closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact_of_value
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hlambda : lambda ≠ 0)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K)
    (hvalue :
      v (supConvolutionTransferPoint lambda η J) =
        compactSupConvolution lambda K v η +
          (lambda / 2) *
            dotProduct (supConvolutionTransferPoint lambda η J - η)
              (supConvolutionTransferPoint lambda η J - η))
    (hJ : J ∈ ClosedSuperjet Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    J ∈ ClosedSuperjet K v (supConvolutionTransferPoint lambda η J) := by
  refine closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact
    (K := K) (v := v) (lambda := lambda) (η := η) (J := J)
    hKne hKcompact hv ?_ hvalue hJ
  intro ξ J' hJ'
  rcases J' with ⟨q, Y⟩
  rcases exists_isMaxOn_supConvolutionKernel_of_isCompact
      (K := K) (u := v) (lambda := lambda) (ξ := ξ) hKne hKcompact hv with
    ⟨y, hy, hmax⟩
  have htransfer :
      supConvolutionTransferPoint lambda ξ ({ gradient := q, hessian := Y } : Jet n) = y :=
    supConvolutionTransferPoint_eq_of_compactSupConvolution_of_isMaxOn
      (K := K) (v := v) (lambda := lambda) (η := ξ) (y := y) (q := q) (Y := Y)
      hlambda
      (fun ζ : Point n =>
        exists_isMaxOn_supConvolutionKernel_of_isCompact
          (K := K) (u := v) (lambda := lambda) (ξ := ζ) hKne hKcompact hv)
      hy hmax hJ'
  simpa [htransfer] using And.intro hy hmax

/--
Closed-superjet transfer for compact sup-convolutions.

In quantified mathematical form, let `K` be nonempty and compact, let `v` be
upper semicontinuous on `K`, and let `lambda ≠ 0`. If `(p, X)` belongs to the
closed superjet of `ξ ↦ compactSupConvolution lambda K v ξ` at `η`, then
`(p, X)` belongs to the closed superjet of `v` at
`η + lambda⁻¹ • p` relative to `K`.
-/
theorem closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact_of_ne_zero
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hlambda : lambda ≠ 0)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K)
    (hJ : J ∈ ClosedSuperjet Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    J ∈ ClosedSuperjet K v (supConvolutionTransferPoint lambda η J) := by
  let vhat : Point n -> Real := fun ξ => compactSupConvolution lambda K v ξ
  let T : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => supConvolutionTransferGraphPoint (n := n) lambda z
  have hTcont : Continuous T := by
    simpa [T] using continuous_supConvolutionTransferGraphPoint (n := n) lambda
  have hT_mem :
      T ((η, vhat η), J) ∈ closure (T '' SuperjetGraph Set.univ vhat) :=
    image_closure_subset_closure_image hTcont ⟨((η, vhat η), J), hJ, rfl⟩
  have hsubset : T '' SuperjetGraph Set.univ vhat ⊆ SuperjetGraph K v := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨ξ, r⟩, J'⟩
    rcases hw with ⟨_hξ, hr, hJ'⟩
    change r = vhat ξ at hr
    subst r
    rcases J' with ⟨q, Y⟩
    rcases exists_isMaxOn_supConvolutionKernel_of_isCompact
        (K := K) (u := v) (lambda := lambda) (ξ := ξ) hKne hKcompact hv with
      ⟨y, hy, hmax⟩
    have htransfer :
        supConvolutionTransferPoint lambda ξ ({ gradient := q, hessian := Y } : Jet n) = y :=
      supConvolutionTransferPoint_eq_of_compactSupConvolution_of_isMaxOn
        (K := K) (v := v) (lambda := lambda) (η := ξ) (y := y) (q := q) (Y := Y)
        hlambda
        (fun ζ : Point n =>
          exists_isMaxOn_supConvolutionKernel_of_isCompact
            (K := K) (u := v) (lambda := lambda) (ξ := ζ) hKne hKcompact hv)
        hy hmax hJ'
    have hJv :
        ({ gradient := q, hessian := Y } : Jet n) ∈
          Superjet K v (supConvolutionTransferPoint lambda ξ
            ({ gradient := q, hessian := Y } : Jet n)) := by
      simpa [htransfer] using
        superjet_of_superjet_compactSupConvolution_of_isMaxOn
          (K := K) (v := v) (lambda := lambda) (η := ξ) (y := y)
          (q := q) (Y := Y)
          (fun ζ : Point n =>
            exists_isMaxOn_supConvolutionKernel_of_isCompact
              (K := K) (u := v) (lambda := lambda) (ξ := ζ) hKne hKcompact hv)
          hy hmax hJ'
    have hvalue_graph :
        supConvolutionTransferValue lambda ξ (vhat ξ)
            ({ gradient := q, hessian := Y } : Jet n) =
          v (supConvolutionTransferPoint lambda ξ ({ gradient := q, hessian := Y } : Jet n)) := by
      have heq := compactSupConvolution_eq_of_isMaxOn
        (K := K) (u := v) (lambda := lambda) (ξ := ξ) (y := y) hy hmax
      change vhat ξ = supConvolutionKernel lambda v ξ y at heq
      dsimp [supConvolutionTransferValue]
      rw [htransfer, heq]
      dsimp [supConvolutionKernel]
      ring
    refine ⟨?_, hvalue_graph, hJv⟩
    change supConvolutionTransferPoint lambda ξ ({ gradient := q, hessian := Y } : Jet n) ∈ K
    simpa only [htransfer] using hy
  have hclosure : T ((η, vhat η), J) ∈ closure (SuperjetGraph K v) :=
    closure_mono hsubset hT_mem
  have hvalue :
      v (supConvolutionTransferPoint lambda η J) =
        compactSupConvolution lambda K v η +
          (lambda / 2) *
            dotProduct (supConvolutionTransferPoint lambda η J - η)
              (supConvolutionTransferPoint lambda η J - η) := by
    refine supConvolutionTransferValue_eq_of_mem_closure_superjetGraph_of_isCompact
      (K := K) (v := v) (lambda := lambda) (η := η) (J := J)
      hKne hKcompact hv ?_
    exact hclosure
  exact closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact_of_value
    (K := K) (v := v) (lambda := lambda) (η := η) (J := J)
    hlambda hKne hKcompact hv hvalue hJ

/--
The compact-set inf-convolution value.

In standard mathematical notation this is

`inf { v(x) + (λ / 2) ∑ i, (x_i - ξ_i)^2 | x ∈ K }`.

It is defined by negating the compact sup-convolution of `-v`, so that the
closed-subjet transfer theorem below is the exact dual of the
closed-superjet transfer theorem for compact sup-convolutions.
-/
def compactInfConvolution (lambda : Real) (K : Set (Point n))
    (v : Point n -> Real) (ξ : Point n) : Real :=
  -compactSupConvolution lambda K (fun x => -v x) ξ

/--
The function whose infimum defines the inf-convolution at `ξ`.

In standard mathematical notation this is

`x ↦ v(x) + (λ / 2) ∑ i, (x_i - ξ_i)^2`.
-/
def infConvolutionKernel (lambda : Real) (v : Point n -> Real) (ξ x : Point n) :
    Real :=
  v x + (lambda / 2) * dotProduct (x - ξ) (x - ξ)

/--
The point selected by the compact inf-convolution transfer map.

In standard mathematical notation, a subjet with first-order part `p` at `η`
transfers to the point `η - λ⁻¹ p`.
-/
def infConvolutionTransferPoint (lambda : Real) (η : Point n) (J : Jet n) :
    Point n :=
  η - lambda⁻¹ • J.gradient

/--
The compact inf-convolution is the negative of the compact sup-convolution of
the negated function.
-/
theorem compactInfConvolution_eq_neg_compactSupConvolution_neg
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real} {η : Point n} :
    compactInfConvolution lambda K v η =
      -compactSupConvolution lambda K (fun x => -v x) η :=
  rfl

/--
The inf-convolution kernel is the negative of the sup-convolution kernel for
the negated function.
-/
theorem infConvolutionKernel_eq_neg_supConvolutionKernel_neg
    (lambda : Real) (v : Point n -> Real) (ξ x : Point n) :
    infConvolutionKernel lambda v ξ x =
      -supConvolutionKernel lambda (fun z : Point n => -v z) ξ x := by
  simp [infConvolutionKernel, supConvolutionKernel]
  ring

/--
If `v` is lower semicontinuous on `K`, then the inf-convolution kernel is
lower semicontinuous on `K`.

In quantified mathematical form, for every real number `λ` and point `ξ`, if
`v` is lower semicontinuous on `K`, then
`x ↦ v x + (λ / 2) * ∑ i, (x i - ξ i)^2` is lower semicontinuous on `K`.
-/
theorem lowerSemicontinuousOn_infConvolutionKernel
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real} {ξ : Point n}
    (hv : LowerSemicontinuousOn v K) :
    LowerSemicontinuousOn (fun x : Point n => infConvolutionKernel lambda v ξ x) K := by
  have hpen :
      ContinuousOn
        (fun x : Point n => (lambda / 2) * dotProduct (x - ξ) (x - ξ)) K := by
    have hdiff : Continuous fun x : Point n => x - ξ :=
      continuous_id.sub continuous_const
    exact (continuous_const.mul (hdiff.dotProduct hdiff)).continuousOn
  have hpenLower :
      LowerSemicontinuousOn
        (fun x : Point n => (lambda / 2) * dotProduct (x - ξ) (x - ξ)) K :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp hpen).1
  simpa [infConvolutionKernel] using hv.add hpenLower

/--
On a nonempty compact set, the inf-convolution kernel attains a minimum.

In quantified mathematical form, if `K` is nonempty and compact and `v` is
lower semicontinuous on `K`, then for every `λ` and `ξ` there exists
`x ∈ K` such that for every `y ∈ K`,

`v x + (λ / 2) * ∑ i, (x i - ξ i)^2 ≤
 v y + (λ / 2) * ∑ i, (y i - ξ i)^2`.
-/
theorem exists_isMinOn_infConvolutionKernel_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real} {ξ : Point n}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : LowerSemicontinuousOn v K) :
    ∃ x ∈ K, IsMinOn (fun y : Point n => infConvolutionKernel lambda v ξ y) K x :=
  LowerSemicontinuousOn.exists_isMinOn hKne hKcompact
    (lowerSemicontinuousOn_infConvolutionKernel hv)

/--
If the inf-convolution kernel has a minimum point `y` on `K`, then the compact
inf-convolution is the kernel value at `y`.

In quantified mathematical form, if `y ∈ K` and for every `z ∈ K`,

`v y + (lambda / 2) * ∑ i, (y i - ξ i)^2 ≤
 v z + (lambda / 2) * ∑ i, (z i - ξ i)^2`,

then

`compactInfConvolution lambda K v ξ =
 v y + (lambda / 2) * ∑ i, (y i - ξ i)^2`.
-/
theorem compactInfConvolution_eq_of_isMinOn
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real} {ξ y : Point n}
    (hy : y ∈ K)
    (hmin : IsMinOn (fun z : Point n => infConvolutionKernel lambda v ξ z) K y) :
    compactInfConvolution lambda K v ξ = infConvolutionKernel lambda v ξ y := by
  have hmax : IsMaxOn (fun z : Point n =>
      supConvolutionKernel lambda (fun w : Point n => -v w) ξ z) K y := by
    intro z hz
    change supConvolutionKernel lambda (fun w : Point n => -v w) ξ z <=
      supConvolutionKernel lambda (fun w : Point n => -v w) ξ y
    have h : infConvolutionKernel lambda v ξ y <=
        infConvolutionKernel lambda v ξ z := hmin hz
    have hy_eq := infConvolutionKernel_eq_neg_supConvolutionKernel_neg lambda v ξ y
    have hz_eq := infConvolutionKernel_eq_neg_supConvolutionKernel_neg lambda v ξ z
    rw [hy_eq, hz_eq] at h
    linarith
  have hsup := compactSupConvolution_eq_of_isMaxOn
    (K := K) (u := fun w : Point n => -v w)
    (lambda := lambda) (ξ := ξ) (y := y) hy hmax
  rw [compactInfConvolution, hsup, infConvolutionKernel_eq_neg_supConvolutionKernel_neg]

/--
The compact inf-convolution transfer point is the compact sup-convolution
transfer point for the negated jet and negated function.
-/
theorem infConvolutionTransferPoint_eq_supConvolutionTransferPoint_neg
    {lambda : Real} {η : Point n} {J : Jet n} :
    infConvolutionTransferPoint lambda η J =
      supConvolutionTransferPoint lambda η J.neg := by
  ext i
  simp [infConvolutionTransferPoint, supConvolutionTransferPoint]
  ring

/--
Lower semicontinuity of `v` gives upper semicontinuity of `-v`.

This local theorem keeps the compact inf-convolution transfer independent of
the viscosity-solution declarations.
-/
theorem lowerSemicontinuousOn_neg_to_upperSemicontinuousOn
    {K : Set (Point n)} {v : Point n -> Real}
    (hv : LowerSemicontinuousOn v K) :
    UpperSemicontinuousOn (fun x => -v x) K := by
  simpa [Function.comp_def] using
    (continuous_neg.comp_lowerSemicontinuousOn_antitone hv
      (fun _ _ h => neg_le_neg h))

/--
Closed-subjet transfer for compact inf-convolutions.

In quantified mathematical form, let `K` be nonempty and compact, let `v` be
lower semicontinuous on `K`, and let `lambda ≠ 0`. If `(p, X)` belongs to the
closed subjet of

`η ↦ inf { v(x) + (lambda / 2) * ∑ i, (x i - η i)^2 | x ∈ K }`

at `η` relative to all of `R^n`, then `(p, X)` belongs to the closed subjet of
`v` at `η - lambda⁻¹ • p` relative to `K`.
-/
theorem closedSubjet_of_closedSubjet_compactInfConvolution_transfer_of_isCompact_of_ne_zero
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η : Point n} {J : Jet n}
    (hlambda : lambda ≠ 0)
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : LowerSemicontinuousOn v K)
    (hJ : J ∈ ClosedSubjet Set.univ
      (fun ξ : Point n => compactInfConvolution lambda K v ξ) η) :
    J ∈ ClosedSubjet K v (infConvolutionTransferPoint lambda η J) := by
  have hJsuper :
      J.neg ∈ ClosedSuperjet Set.univ
        (fun ξ : Point n => -compactInfConvolution lambda K v ξ) η :=
    closedSubjet_neg_to_closedSuperjet hJ
  have hJsuper' :
      J.neg ∈ ClosedSuperjet Set.univ
        (fun ξ : Point n => compactSupConvolution lambda K (fun x => -v x) ξ) η := by
    simpa [compactInfConvolution] using hJsuper
  have hvneg : UpperSemicontinuousOn (fun x : Point n => -v x) K :=
    lowerSemicontinuousOn_neg_to_upperSemicontinuousOn hv
  have htransfer :
      J.neg ∈ ClosedSuperjet K (fun x : Point n => -v x)
        (supConvolutionTransferPoint lambda η J.neg) :=
    closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact_of_ne_zero
      (K := K) (v := fun x : Point n => -v x) (lambda := lambda)
      (η := η) (J := J.neg) hlambda hKne hKcompact hvneg hJsuper'
  have hsub :
      J.neg.neg ∈ ClosedSubjet K (fun x : Point n => -(-v x))
        (supConvolutionTransferPoint lambda η J.neg) :=
    closedSuperjet_neg_to_closedSubjet htransfer
  have hnegneg : J.neg.neg = J := by
    cases J
    simp [Jet.neg]
  simpa [hnegneg, infConvolutionTransferPoint_eq_supConvolutionTransferPoint_neg] using hsub

end ViscositySolns
