# Sources, licenses, and attribution

Original project code is distributed under Apache-2.0. Applicable third-party
licenses and notices are preserved; the root license does not override them.

- Public API: `AcceleratedLogConcave/WarmStart.lean`.
- Mathlib: pinned in `lakefile.toml` and `lake-manifest.json`; fetched separately,
  not included in the source artifact.
- OpenAI mathematical proof ports: `AcceleratedLogConcave/External/OAI/PROVENANCE.json` records upstream
  repository, revision and selected files. Apache-2.0 license text is retained in
  that directory. `AcceleratedLogConcave/External/HeatCalculus/Upstream/LICENSE.openai-math` is retained
  for its corresponding proof material; source headers identify upstream files.
- Michael R. Douglas's Markov semigroup proofs: see
  `AcceleratedLogConcave/External/MarkovSemigroups/UPSTREAM.md` and its LICENSE.
- Samplinglib: 29 selected modules from
  https://github.com/DakeBU/Automization-Sampling-Optimisation-Geometry-Lib,
  revision `933dd38de9423d2967bc36b501b3a2006343000d`.
  An express Apache-2.0 historical grant was merged at `9f7a7419ea401547c71c5c2890380ec357fa983a`,
  covering project-original versions of these modules at the pinned revision.
  Current LICENSE, NOTICE, LICENSE_SCOPE.md and UPSTREAM_NOTICE.md are retained
  in the Samplinglib directory. Cutoff retains its original Yuanhe Zhang notice.
  The scope states an effective date of November 3, 2026 without a timezone.
- Scott Armstrong's LeanAutoformalizationSkills supplied workflow guidance, not
  a mathematical or Lake dependency. See README for the exact revision, credit,
  and CC BY 4.0 link. No skill files are redistributed here.

Third-party copyright, license, attribution and modification notices are preserved. The top-level SHA256SUMS covers
this source-only artifact; internal logs and build dependencies are not deliverables.
