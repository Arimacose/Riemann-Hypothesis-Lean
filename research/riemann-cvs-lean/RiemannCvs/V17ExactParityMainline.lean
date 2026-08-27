import RiemannCvs.CommonLeadingWeilTransfer
import RiemannCvs.OddTempleParityTransfer
import RiemannCvs.SymmetrizedProlateBridge
import RiemannCvs.SymmetrizedProlateSecular
import RiemannCvs.SymmetrizedProlateGap
import RiemannCvs.ProlateConductorIdentity
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
4. defect-weighted conductor coercivity;
5. common-leading Weil transfer and odd-sector Temple budgets.

The analytic PSWF exterior estimates, closed-form radical extension, prime
oscillatory bound, and actual odd-sector spectral gap are not asserted by this
module.
-/
