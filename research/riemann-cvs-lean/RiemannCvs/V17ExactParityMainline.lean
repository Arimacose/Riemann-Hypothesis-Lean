import RiemannCvs.CommonLeadingWeilTransfer
import RiemannCvs.OddTempleParityTransfer
import RiemannCvs.SymmetrizedProlateBridge
import RiemannCvs.SymmetrizedProlateSecular
import RiemannCvs.SymmetrizedProlateGap
import RiemannCvs.ProlateDilationStationaryPoint
import RiemannCvs.ProlateConductorIdentity
import RiemannCvs.ExteriorLogMomentTransfer
import RiemannCvs.ConductorDefectCoercivity
import RiemannCvs.NormalizedSymmetrizedConductor

/-!
# V17 exact-parity prolate mainline

This umbrella module contains no additional theorem.  Its purpose is to force a
single Lean build to elaborate the finite-dimensional and algebraic pieces of
the revised main line:

1. exact Fourier symmetrization of compressed prolate modes;
2. preservation of fixed-index defects, residues, and gaps;
3. exact logarithmic conductor identity for the leakage tail;
4. explicit compact-interval Dunster phase primitive, weight, mass, derivative,
   prolate slope, curvature, and reduced-weight variation bounds, including the
   concrete
   `c ≥ 33` weighted-cosine lower bound and the `48 K² ≤ c²`
   fixed-interval remainder-absorption budget.  A source-shaped refinement
   keeps the Dunster and Bessel-to-cosine errors separate and closes them under
   `96 * (K_d² + K_b²) ≤ c²`, followed by the conductor-ready
   `288 * upper` logarithmic-moment compositions,
   weighted oscillatory-average and `L²` remainder budgets, explicit
   hyperbolic-envelope integration, exact one-sided DLMF concentration
   normalization, and transfer to the physical logarithmic-moment bounds;
5. defect-weighted conductor coercivity;
6. common-leading Weil transfer and odd-sector Temple budgets.

The source-specific Dunster and Bessel estimates supplying the two pointwise
`K / c` errors in the repository's normalization, their parameter thresholds
and identification with the normalized phase primitive, closed-form radical
extension, prime oscillatory bound, and actual odd-sector spectral gap are not
asserted by this module.
-/
