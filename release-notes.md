# Initial manuscript release

**The manuscript content is AI-generated.** These initial drafts combine OpenAI’s released work with our existing ongoing research and ideas; improved understanding and exposition are in preparation.

This release collects two initial research drafts on accelerated sampling with subpolynomial dimension dependence. Our understanding and exposition are still being refined, and clearer, more polished accounts are forthcoming. Corrections and feedback are welcome.

## Read the manuscripts

- **Cold accelerated sampling with subpolynomial dimension dependence:** [Read the PDF](https://github.com/jianfenglu/accelerated-logconcave-sampling/blob/main/manuscripts/cold-start.pdf)
- **Warm-start sampling with square-root condition-number dependence:** [Read the PDF](https://github.com/jianfenglu/accelerated-logconcave-sampling/blob/main/manuscripts/warm-start.pdf)

## Results in brief

The first draft gives a $C_\eta\kappa^{2/3}d^\eta$ every-execution query bound at fixed total variation accuracy for each fixed $\eta>0$. Its cold initialization uses at most one exact positive-scalar proximal query; a supplied near-center point satisfying the manuscript's gradient condition makes the algorithm gradient-only. The large-condition-number branch uses standard BPS with windowed thinning.

The second draft gives a $C\sqrt{\kappa}\,d^\eta$ every-execution original-gradient bound from a supplied polynomial squared-$L^2$ warm start, at fixed total variation accuracy, for sufficiently large $d$ and $\kappa\le d^{100}$. Warm-start preparation is excluded. It does not establish a general cold-start bound at this rate.

The precise assumptions, initialization conventions, constants, and oracle models are in the manuscripts. These are exact-real query bounds, rather than finite-bit running-time guarantees.

## Included in this release

- The $\kappa^{2/3}$ cold-sampling manuscript, 73 pages
- The warm-start manuscript, 73 pages
- Manuscript provenance and SHA-256 checksums
- The Apache 2.0 license for adapted OpenAI analytic material

## Attribution

The PDFs include explicit result-level OpenAI citations, a 30-entry source-correspondence appendix, and adaptation/license notices. They distinguish inherited results and constructions from the additional arguments developed for these samplers, and retain the earlier numerical, accelerated-sampling, and hypocoercivity references.

## Research status

These manuscripts are preliminary research drafts. The arguments and exposition remain subject to further scrutiny. No complete independent verification of the proofs is claimed. The statements should be read with their explicit hypotheses and the qualifications above.

## Feedback

Questions, corrections, and suggestions for improving the proofs or exposition are welcome. Please include the manuscript title and the relevant section or equation.
