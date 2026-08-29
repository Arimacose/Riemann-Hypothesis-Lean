import RiemannCvs.V22ZeroModeMainline
import RiemannCvs.BoundaryWeylCumulative
import RiemannCvs.BoundaryGapNoCrossing
import RiemannCvs.ParityOrderContinuation
import RiemannCvs.PiecewiseParityContinuation

/-!
# V23 boundary-Weyl no-crossing mainline

This umbrella extends the checked V22 zero-mode surface with the finite
boundary-Weyl layer recovered from the subsequent research argument.

The new kernel-checked chain contains:

1. finite Abel summation for a residue sequence and decreasing weights;
2. strict positivity from nonnegative proper cumulative residues and a
   strictly positive final cumulative residue;
3. positivity and nonvanishing of the boundary-Weyl function everywhere
   before its first pole;
4. exclusion of a factorized numerator root in that region;
5. preservation of the scalar sign through the V22 negative rank-one
   correction denominator;
6. the repaired boundary-gap obstruction, continuous no-crossing propagation,
   and order preservation across rank-one prime events.

This is a reduction layer, not a hidden continuum estimate.  Applying it to
the full CvS family still requires a concrete displacement/determinant
identity, rigorous cumulative-residue bounds uniform in the cutoff, spectral
continuity and compactness, and the remaining source-specific exterior
remainder estimate.
-/
