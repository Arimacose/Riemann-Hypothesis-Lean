import RiemannCvs.CommonLeadingWeilTransfer
import RiemannCvs.OddTempleParityTransfer
import RiemannCvs.SymmetrizedProlateBridge
import RiemannCvs.SymmetrizedProlateSecular
import RiemannCvs.SymmetrizedProlateGap
import RiemannCvs.ProlateDilationStationaryPoint
import RiemannCvs.ProlateConductorIdentity
import RiemannCvs.BesselJ0IntegralRepresentation
import RiemannCvs.BesselJ0Dlmf
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
   `96 * (K_d² + K_b²) ≤ c²`.  The canonical cosine reference discharges its
   square identity and integrability internally, `a ≤ parameterK / c` enters
   the fixed rectangle under `2 * parameterK ≤ c`, and any source phase with
   the same slope is proved to differ by one explicit offset.  The concrete
   Dunster four-root prefactor, a concrete everywhere-convergent real `J₀`
   series, the corresponding intermediate, and both difference-error functions
   are now defined internally.  The series is proved summable at every real
   argument, continuous, even, normalized by `J₀(0) = 1`, twice differentiable,
   and equipped with its Bessel coefficient recurrence.  Its termwise first and
   second derivative series satisfy `J₀'(0) = 0`, `J₀''(0) = -1/2`, and the
   order-zero Bessel differential equation on the whole real axis.  A direct
   dominated-convergence argument now also identifies this series with the
   Poisson--Schlafli integral
   `π⁻¹ ∫ t in 0..π, cos (x * sin t)` for every real `x`.
   Source-phase positivity and all
   continuity/integrability adapters are discharged from the phase derivative,
   `sourcePhase 2 ≥ 1`, continuity of `J₀`, and continuity of the actual radial
   mode.  DLMF 10.17.1 is specialized internally at order zero, proving
   `a₀ = 1`, `a₁ = -1/8`, `a₂ = 9/128`, and `a₃ = -75/1024`; the separate
   first-neglected even/odd remainder bounds are combined into the exact
   three-term absolute-error envelope and then lifted automatically from a
   single global positive-axis DLMF predicate to the source interval.  These
   feed the conductor-ready
   `288 * upper` logarithmic-moment compositions,
   weighted oscillatory-average and `L²` remainder budgets, explicit
   hyperbolic-envelope integration, exact one-sided DLMF concentration
   normalization, and transfer to the physical logarithmic-moment bounds;
5. defect-weighted conductor coercivity;
6. common-leading Weil transfer and odd-sector Temple budgets.

The source-specific analytic inputs still to be supplied are Dunster's uniform
PSWF-to-Bessel remainder in the repository normalization, a concrete
`a ≤ parameterK / c` constant and eventual threshold, and the analytic
construction of the even and odd real-argument DLMF remainders for the concrete
repository `J₀` series by a quantitative stationary-phase analysis of the proved
oscillatory integral.  Their coefficient
specialization, first-neglected-term
combination, source-interval specialization, and conductor adapters are now
formalized.  The
closed-form radical extension, prime
oscillatory bound, and actual odd-sector spectral gap are also not asserted by
this module.
-/
