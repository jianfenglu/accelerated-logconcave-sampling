# Theorem correspondence

The selected attributed companion is a **46-page PDF**, SHA-256
`9505584a55c0906104d5da5901a5d0b7d0c2562cc8b247f86a9882de73c547c8`.
This identifies the citation-reviewed companion manuscript. Its identity and main-results correspondence have been checked. Any later manuscript change requires an updated correspondence review.

The older public warm-start PDF SHA-256
`c312f9ecf492e5bb9f407cd12e740a6f72ec6baee1a9f7f078ce69e5d1cd07da`
is a comparison baseline only, not the selected exact companion.

| Manuscript statement | Lean declaration | Correspondence and limitations |
|---|---|---|
| Theorem 1.1 | `AcceleratedLogConcave.WarmStart.accelerated_warm_start` | Accuracy of returned law and every-execution gradient-query bound under supplied joint phase-warmness, C² curvature bounds, κ ≤ D^100 and dimension threshold. No cold-start or bit-complexity claim. |
| Theorem 1.1: accuracy | `AcceleratedLogConcave.WarmStart.implemented_error` | TV error ≤ ε. Analytic accuracy and local KL certificates are proved internally, not arguments of this endpoint. |
| Theorem 1.1: parameter positivity | `AcceleratedLogConcave.WarmStart.public_parameters` | Positivity of exponent and work constant under η > 0, Cw ≥ 0, 0 < ε < 1/4. |
| Corollary 1.2 | `AcceleratedLogConcave.WarmStart.original_target_warm_error` | Gaussian initialization of a supplied original-target-warm positional law. Endpoint explicitly concludes accuracy; the unchanged sampler's work bound is the preceding theorem. |

**Revised manuscript Theorem 1.3 is NOT FORMALIZED by this release.**
Its presence in the companion manuscript does not expand this package’s
Theorem 1.1 / Corollary 1.2 scope.

Lean admits Cw = 0; the inspected public statement uses Cw > 0, a special case.
The manuscript defines warmness as the squared density integral. Lean uses
`L2Warm reference input bound`, with explicit absolute continuity and squared-density
integrability. The phase reference is the smoothed target at variance `2*h^2`
times independent standard Gaussian momentum. The original-target initialization
is `X0 = A0 + sqrt(2)*h*Z0`, with an independent standard Gaussian momentum,
matching Corollary 1.2 exactly. The Lean exponent is chosen as
`min (eta/3) (1/100)` and its dimension threshold depends only on the fixed
accuracy, exponent and warmness parameters.
The formal sampler is a noncomputable probability/oracle model, not a released
executable numerical sampler. Its trace query counts do not include sampling the
supplied warm input or costs outside the stated oracle model.
