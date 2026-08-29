import RiemannCvs.ZeroModeCorrection
import RiemannCvs.BoundaryRankOneGap
import RiemannCvs.SchurQuadraticForm
import RiemannCvs.NormalizedBlockSchur
import RiemannCvs.V17ExactParityMainline

/-!
# V22 zero-mode corrected mainline

This umbrella is the repository-side successor to the historical V17 exact-
parity umbrella.  It adds the corrected cutoff-free `n = 0` archimedean term
and its negative rank-one matrix update, while retaining the already-checked
stationary-phase, Schur, rank-one boundary, and prolate transfer modules.

The new theorem surface proves:

1. positivity of finite `G₁` and `G₂` zero-mode partial sums;
2. `X_C(0) = X₀ - L G₁ - G₂` is strictly below the uncorrected value;
3. the cutoff-free entry is updated by
   `T_new = T_old - (2 G₁ + 2 G₂/L) e₀ e₀ᵀ`;
4. the correction is invisible on the zero-coordinate (in particular odd)
   sector and strictly lowers vectors with nonzero zero-mode overlap.

The companion numerical audit identifies the infinite sums with the concrete
closed form at `c = 13` and the Arb certificate replays the finite parity gap.
No continuum no-crossing conclusion is asserted by this import surface alone.
-/
