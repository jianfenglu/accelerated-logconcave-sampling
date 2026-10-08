# Manuscripts and sources

This repository contains two initial research manuscripts in PDF format. Their precise theorem statements, assumptions, and source attributions are given in the PDFs.

## Cold accelerated sampling

- Title: *Cold accelerated sampling with subpolynomial dimension dependence*
- File: `manuscripts/cold-start.pdf`
- Length: 73 pages
- Scope: cold-start sampling with an every-execution query cap; at most one exact proximal initialization query, or gradients only with the stated supplied near-center point
- SHA-256: `c974af85a6b7e9f7a8f9379f6a023c8f9c29f4ea95dcea4c32b4dfa85ee95768`

## Warm-start sampling

- Title: *Warm-start sampling with square-root condition-number dependence*
- File: `manuscripts/warm-start.pdf`
- Length: 73 pages
- Scope: supplied-warm, fixed-accuracy original-gradient sampling under the dimension and condition-number restrictions in the main theorem
- SHA-256: `c312f9ecf492e5bb9f407cd12e740a6f72ec6baee1a9f7f078ce69e5d1cd07da`

## Attribution

The manuscripts identify adapted analytic results and proofs from OpenAI's *Subpolynomial query complexity for well-conditioned log-concave sampling*, September 26, 2026. The source is pinned to [the manuscript and its sources at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026).

Each PDF contains source citations beside the inherited results, a 30-entry correspondence appendix, and an adaptation/license notice. The inherited sampling Gaussian reserve, conditional-mean machinery, recursive evaluation, Gaussian absorption, and conditional-descent construction are credited separately from the manuscript-specific developments. Earlier numerical, accelerated-sampling, and hypocoercivity references are retained and identified in the bibliographies.

OpenAI is the immediate source of the adapted statements and proofs, not necessarily the original source of every standard ingredient. Adapted material is reused under the [Apache License 2.0](LICENSE). No endorsement by OpenAI is implied.

These are preliminary research drafts. Source attribution and editorial checks do not constitute a complete independent verification of the proofs.

## Contributor contact details

The README credits name the contributors to this research release. The affiliations and email addresses were checked against the first-page author listings of the following recent preprints:

- [arXiv:2610.06308v1, October 5, 2026](https://arxiv.org/pdf/2610.06308v1): Fan Chen, Sinho Chewi, Jianfeng Lu, and Matthew S. Zhang.
- [arXiv:2609.15884v1, September 14, 2026](https://arxiv.org/pdf/2609.15884v1): Yunbum Kook.

The README contributor credits are separate from the manuscripts.
