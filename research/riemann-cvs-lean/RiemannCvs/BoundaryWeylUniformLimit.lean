import RiemannCvs.BoundaryWeylCumulative

/-!
# Uniform boundary-Weyl limit bridge

Strict positivity of every finite Galerkin function is not by itself closed
under passage to a limit: the positive margin could shrink to zero.  This
module records the two quantitative interfaces that make the transfer valid.

1. An eventual lower bound `margin > 0` passes through pointwise convergence.
2. At one certified cutoff, a finite lower bound `2 * margin` and a uniform
   truncation error at most `margin` leave a positive limiting margin.

Together with the quantitative Abel theorems, the second route reduces the
analytic input to either the final-term comparison

`2 * margin <= final cumulative residue / final pole distance`,

or the corresponding bound from an earlier cumulative reciprocal-weight drop,
plus a tail/resolvent error no larger than `margin`.  No compactness, operator
convergence, or source-specific CvS estimate is hidden here; those remain
visible hypotheses.
-/

namespace RiemannCvs.BoundaryWeylUniformLimit

open Filter
open RiemannCvs.BoundaryWeylCumulative

variable {X : Type*}

/-- A common eventual lower bound survives pointwise real convergence. -/
theorem lowerBoundOn_of_pointwiseLimit
    (approx : ℕ → X → ℝ) (limit : X → ℝ)
    (domain : Set X) (margin : ℝ)
    (hTendsto : ∀ x ∈ domain,
      Tendsto (fun N => approx N x) atTop (nhds (limit x)))
    (hLower : ∀ x ∈ domain,
      ∀ᶠ N in atTop, margin ≤ approx N x) :
    ∀ x ∈ domain, margin ≤ limit x := by
  intro x hx
  exact ge_of_tendsto (hTendsto x hx) (hLower x hx)

/-- A strictly positive uniform margin therefore rules out zeros of the
pointwise limit on the whole stated domain. -/
theorem positiveOn_of_pointwiseLimit_uniformMargin
    (approx : ℕ → X → ℝ) (limit : X → ℝ)
    (domain : Set X) (margin : ℝ)
    (hMargin : 0 < margin)
    (hTendsto : ∀ x ∈ domain,
      Tendsto (fun N => approx N x) atTop (nhds (limit x)))
    (hLower : ∀ x ∈ domain,
      ∀ᶠ N in atTop, margin ≤ approx N x) :
    ∀ x ∈ domain, 0 < limit x := by
  intro x hx
  exact lt_of_lt_of_le hMargin
    (lowerBoundOn_of_pointwiseLimit
      approx limit domain margin hTendsto hLower x hx)

/-- Nonvanishing formulation of the pointwise uniform-margin transfer. -/
theorem nonzeroOn_of_pointwiseLimit_uniformMargin
    (approx : ℕ → X → ℝ) (limit : X → ℝ)
    (domain : Set X) (margin : ℝ)
    (hMargin : 0 < margin)
    (hTendsto : ∀ x ∈ domain,
      Tendsto (fun N => approx N x) atTop (nhds (limit x)))
    (hLower : ∀ x ∈ domain,
      ∀ᶠ N in atTop, margin ≤ approx N x) :
    ∀ x ∈ domain, limit x ≠ 0 := by
  intro x hx
  exact ne_of_gt (positiveOn_of_pointwiseLimit_uniformMargin
    approx limit domain margin hMargin hTendsto hLower x hx)

/-- A single finite approximation with twice the target margin remains
positive after an error of at most one margin.  This is the direct finite
certificate plus tail-budget interface. -/
theorem positiveOn_of_finiteMargin_and_uniformError
    (approx limit : X → ℝ) (domain : Set X) (margin : ℝ)
    (hMargin : 0 < margin)
    (hApprox : ∀ x ∈ domain, 2 * margin ≤ approx x)
    (hError : ∀ x ∈ domain,
      |approx x - limit x| ≤ margin) :
    ∀ x ∈ domain, 0 < limit x := by
  intro x hx
  have hDiff : approx x - limit x ≤ margin :=
    le_trans (le_abs_self (approx x - limit x)) (hError x hx)
  linarith [hApprox x hx]

/-- Sequence form specialized to Galerkin boundary-Weyl functions.  A common
eventual lower bound on the last Abel terms propagates through the entire
finite sums and then through pointwise convergence. -/
theorem boundaryWeylLimit_pos_of_uniformFinalTerms
    (poles residues : ℕ → ℕ → ℝ) (cutoff : ℕ → ℕ)
    (x limitValue margin : ℝ)
    (hMargin : 0 < margin)
    (hPoles : ∀ n, StrictMono (poles n))
    (hBefore : ∀ n, x < poles n 0)
    (hProperPrefix : ∀ n j, j < cutoff n →
      0 ≤ prefixSum (residues n) j)
    (hFinalTerm : ∀ᶠ n in atTop,
      margin ≤ prefixSum (residues n) (cutoff n) /
        (poles n (cutoff n) - x))
    (hTendsto :
      Tendsto
        (fun n => finiteBoundaryWeyl
          (poles n) (residues n) (cutoff n) x)
        atTop (nhds limitValue)) :
    0 < limitValue := by
  apply lt_of_lt_of_le hMargin
  apply ge_of_tendsto hTendsto
  exact hFinalTerm.mono (fun n hn =>
    hn.trans (finiteBoundaryWeyl_ge_finalCumulativeTerm
      (poles n) (residues n) (cutoff n) x
      (hPoles n) (hBefore n) (hProperPrefix n)))

/-- Stronger sequence route using one fixed proper Abel prefix.  Unlike the
last term, such an early reciprocal-weight drop need not decay when the
largest Galerkin pole escapes to infinity. -/
theorem boundaryWeylLimit_pos_of_uniformPrefixDrops
    (poles residues : ℕ → ℕ → ℝ) (cutoff : ℕ → ℕ)
    (k : ℕ) (x limitValue margin : ℝ)
    (hMargin : 0 < margin)
    (hCutoff : ∀ n, k < cutoff n)
    (hPoles : ∀ n, StrictMono (poles n))
    (hBefore : ∀ n, x < poles n 0)
    (hPrefix : ∀ n j, j ≤ cutoff n →
      0 ≤ prefixSum (residues n) j)
    (hPrefixDrop : ∀ᶠ n in atTop,
      margin ≤ prefixSum (residues n) k *
        (1 / (poles n k - x) -
          1 / (poles n (k + 1) - x)))
    (hTendsto :
      Tendsto
        (fun n => finiteBoundaryWeyl
          (poles n) (residues n) (cutoff n) x)
        atTop (nhds limitValue)) :
    0 < limitValue := by
  apply lt_of_lt_of_le hMargin
  apply ge_of_tendsto hTendsto
  exact hPrefixDrop.mono (fun n hn =>
    hn.trans (finiteBoundaryWeyl_ge_prefixDrop
      (poles n) (residues n) (cutoff n) k x
      (hCutoff n) (hPoles n) (hBefore n) (hPrefix n)))

/-- Concrete one-cutoff boundary-Weyl transfer.  The final Abel term supplies
the finite `2 * margin` certificate, and the remaining hypothesis is exactly
the uniform finite-to-limit error budget. -/
theorem boundaryWeylLimit_pos_of_oneCutoffError
    (poles residues : ℕ → ℝ) (N : ℕ)
    (x limitValue margin : ℝ)
    (hMargin : 0 < margin)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix :
      ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalTerm :
      2 * margin ≤ prefixSum residues N / (poles N - x))
    (hError :
      |finiteBoundaryWeyl poles residues N x - limitValue| ≤ margin) :
    0 < limitValue := by
  have hFinite :
      2 * margin ≤ finiteBoundaryWeyl poles residues N x :=
    hFinalTerm.trans (finiteBoundaryWeyl_ge_finalCumulativeTerm
      poles residues N x hPoles hBefore hProperPrefix)
  have hDiff :
      finiteBoundaryWeyl poles residues N x - limitValue ≤ margin :=
    le_trans
      (le_abs_self
        (finiteBoundaryWeyl poles residues N x - limitValue))
      hError
  linarith

/-- The same one-cutoff budget in the no-zero form used by the characteristic
factorization layer. -/
theorem boundaryWeylLimit_ne_zero_of_oneCutoffError
    (poles residues : ℕ → ℝ) (N : ℕ)
    (x limitValue margin : ℝ)
    (hMargin : 0 < margin)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hProperPrefix :
      ∀ j, j < N → 0 ≤ prefixSum residues j)
    (hFinalTerm :
      2 * margin ≤ prefixSum residues N / (poles N - x))
    (hError :
      |finiteBoundaryWeyl poles residues N x - limitValue| ≤ margin) :
    limitValue ≠ 0 :=
  ne_of_gt (boundaryWeylLimit_pos_of_oneCutoffError
    poles residues N x limitValue margin hMargin hPoles hBefore
    hProperPrefix hFinalTerm hError)

/-- One-cutoff error-budget route using an early Abel prefix rather than the
possibly decaying final term. -/
theorem boundaryWeylLimit_pos_of_prefixDropError
    (poles residues : ℕ → ℝ) (N k : ℕ)
    (x limitValue margin : ℝ)
    (hMargin : 0 < margin)
    (hk : k < N)
    (hPoles : StrictMono poles)
    (hBefore : x < poles 0)
    (hPrefix : ∀ j, j ≤ N → 0 ≤ prefixSum residues j)
    (hPrefixDrop :
      2 * margin ≤ prefixSum residues k *
        (1 / (poles k - x) -
          1 / (poles (k + 1) - x)))
    (hError :
      |finiteBoundaryWeyl poles residues N x - limitValue| ≤ margin) :
    0 < limitValue := by
  have hFinite :
      2 * margin ≤ finiteBoundaryWeyl poles residues N x :=
    hPrefixDrop.trans (finiteBoundaryWeyl_ge_prefixDrop
      poles residues N k x hk hPoles hBefore hPrefix)
  have hDiff :
      finiteBoundaryWeyl poles residues N x - limitValue ≤ margin :=
    le_trans
      (le_abs_self
        (finiteBoundaryWeyl poles residues N x - limitValue))
      hError
  linarith

/-- Compact-interval version that composes directly with an Arb-certified
left-endpoint prefix margin.  A uniform resolvent-tail error below half that
finite margin proves positivity of the limiting Weyl function on the whole
interval. -/
theorem boundaryWeylLimit_posOn_Icc_of_prefixDropAtLeftError
    (poles residues : ℕ → ℝ) (N k : ℕ)
    (xLeft xRight : ℝ) (limit : ℝ → ℝ) (margin : ℝ)
    (hMargin : 0 < margin)
    (hk : k < N)
    (hPoles : StrictMono poles)
    (hRightBefore : xRight < poles 0)
    (hPrefix : ∀ j, j ≤ N → 0 ≤ prefixSum residues j)
    (hPrefixDropAtLeft :
      2 * margin ≤ prefixSum residues k *
        (1 / (poles k - xLeft) -
          1 / (poles (k + 1) - xLeft)))
    (hError : ∀ x ∈ Set.Icc xLeft xRight,
      |finiteBoundaryWeyl poles residues N x - limit x| ≤ margin) :
    ∀ x ∈ Set.Icc xLeft xRight, 0 < limit x := by
  intro x hx
  have hBefore : x < poles 0 := lt_of_le_of_lt hx.2 hRightBefore
  have hFinite :
      2 * margin ≤ finiteBoundaryWeyl poles residues N x :=
    hPrefixDropAtLeft.trans
      (finiteBoundaryWeyl_ge_prefixDropAtLeft
        poles residues N k xLeft x hk hPoles hx.1 hBefore hPrefix)
  have hDiff :
      finiteBoundaryWeyl poles residues N x - limit x ≤ margin :=
    le_trans
      (le_abs_self (finiteBoundaryWeyl poles residues N x - limit x))
      (hError x hx)
  linarith

end RiemannCvs.BoundaryWeylUniformLimit
