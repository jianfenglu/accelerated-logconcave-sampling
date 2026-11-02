# Warm-start accelerated log-concave sampling: Lean formalization

This directory contains the source formalization, pinned build configuration and endpoint-audit programs.

## Scope and theorem entry points

Read `AcceleratedLogConcave/WarmStart.lean`:

- `AcceleratedLogConcave.WarmStart.accelerated_warm_start`: Theorem 1.1,
  total-variation accuracy and an original-gradient query bound for every
  complete execution, starting from a supplied phase-warm sample.
- `AcceleratedLogConcave.WarmStart.original_target_warm_error`: Corollary 1.2,
  accuracy after Gaussian initialization from an original-target-warm sample.
  The query bound follows from the same sampler's theorem; this particular
  corollary declaration states accuracy, not the combined accuracy/work conjunction.
- `implemented_error` and `public_parameters` expose accuracy and positivity
  of the chosen constants separately.

The assumptions include η > 0, Cw ≥ 0, 0 < ε < 1/4, sufficiently large
integer dimension D, 1 ≤ κ ≤ D^100, a C² potential V with Hessian bounded
between κ⁻¹ I and I, and a supplied probability law with the stated squared-L²
warmness bound D^Cw. The dimension threshold and work constant depend on η,
Cw and ε. Accuracy refers to the actual returned law, and work counts original
potential-gradient queries. Preparing the supplied warm sample, bit complexity,
and general cold-start guarantees are not claims of this formalization.
No cold-start theorem is included or asserted. Revised manuscript Theorem 1.3
is not formalized by this release.

## Toolchain and build

The source pins Lean `leanprover/lean4:v4.34.1` and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`; retain `lake-manifest.json`.
With the pinned Lean toolchain already installed and dependencies available:

```sh
lake --wfail build
lake env lean -DwarningAsError=true AuditEndpoints.lean
lake env lean -DwarningAsError=true AuditClosure.lean
lake env lean -DwarningAsError=true Example.lean
```

`AuditEndpoints` prints cached axiom lists. `AuditClosure` independently traverses
the checked types and values reachable from the four endpoints and rejects axioms
other than `propext`, `Classical.choice`, and `Quot.sound`. This endpoint audit is
not an all-module declaration audit. `Example` checks the consumer imports.

## Provenance and acknowledgments

Mathematical sources and imported third-party modules retain their original
notices. A repository-level license does not override third-party notices or
establish rights in sources whose redistribution status is still unresolved.

We acknowledge Scott Armstrong's
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
(commit `05a07311f16bc581729e52f3e73647b95fa9bef1`) for workflow guidance on
proof architecture, library search, and dependency planning. Its original
skills and reference material are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
This was workflow guidance, not a mathematical theorem assumption or a Lake
package dependency. This extraction does not redistribute those skill files.
