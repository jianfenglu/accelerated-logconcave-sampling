# Accelerated Logconcave Sampling

Initial research drafts on accelerated sampling with subpolynomial dimension dependence.

**The manuscript content is AI-generated.** These initial drafts combine OpenAI’s released work with our existing ongoing research and ideas; improved understanding and exposition are in preparation.

**Preliminary status.** These are initial drafts. Our understanding of the arguments and their presentation is still developing, and improved explanations and exposition are forthcoming. Corrections, questions, and suggestions are welcome.

## Manuscripts

### 1. Cold accelerated sampling with subpolynomial dimension dependence

[Read the PDF](manuscripts/cold-start.pdf)

For each fixed $\eta>0$, this draft gives an every-execution query bound of $C_\eta\kappa^{2/3}d^\eta$ at total variation accuracy $1/10$ for a $C^2$ strongly convex potential with supplied positive lower and upper Hessian bounds. Here $d$ is the dimension and $\kappa$ is the ratio of those bounds.

The oracle model counts original gradients and exact positive-scalar proximal queries. At most one proximal query is used, in initialization. With a supplied point satisfying $\|\nabla V(x_{\rm ref})\|\le\sqrt{\alpha d}$, where $\alpha$ is the supplied lower Hessian bound, the algorithm uses gradients alone for every condition number. The draft also states an arbitrary-accuracy consequence with separately chosen positive powers of dimension and inverse accuracy.

The manuscript has 73 pages. Its large-condition-number branch uses standard BPS with windowed thinning.

### 2. Warm-start sampling with square-root condition-number dependence

[Read the PDF](manuscripts/warm-start.pdf)

For each fixed $\eta>0$, fixed total variation accuracy, and a supplied polynomial squared-$L^2$ warmness bound, this draft gives an every-execution bound of $C\sqrt{\kappa}\,d^\eta$ original-gradient queries. The result assumes sufficiently large dimension and $1\le\kappa\le d^{100}$; the constants and dimension threshold depend on the fixed accuracy, exponent, and warmness bound.

The warm input is supplied, and its preparation is not counted. This manuscript does not supply a general cold-start $\sqrt{\kappa}\,d^\eta$ theorem. The precise input spaces, curvature normalization, and initialization options are stated in the main theorem and its corollary.

The manuscript has 73 pages and uses a latent-state construction with simultaneous Picard iteration.

## Files

- The manuscripts above contain the precise statements, assumptions, and proofs.
- [Manuscripts and sources](SOURCES.md) records the PDF checksums and the sources of inherited material.
- [SHA-256 checksums](SHA256SUMS) identify the exact manuscript files.

Both query bounds use exact-real computation conventions. They are not arithmetic-runtime or finite-bit complexity bounds. Fixed approximation orders and their constants should be read as stated in each manuscript; no uniform polylogarithmic inverse-accuracy guarantee is asserted.

## Attribution

These results were obtained by combining OpenAI’s released work with our existing ongoing research and ideas.

The manuscripts retain their citations and attribution for earlier work. In particular, adapted analytic material from OpenAI's *Subpolynomial query complexity for well-conditioned log-concave sampling* is accompanied by its [Apache License 2.0](LICENSE).

## Contributors

- Fan Chen, Department of Electrical Engineering and Computer Science, MIT. Email: [fanchen@mit.edu](mailto:fanchen@mit.edu).
- Sinho Chewi, Department of Statistics and Data Science, Yale University. Email: [sinho.chewi@yale.edu](mailto:sinho.chewi@yale.edu).
- Yunbum Kook, University of Michigan. Email: [ybkook@umich.edu](mailto:ybkook@umich.edu).
- Jianfeng Lu, Department of Mathematics, Duke University. Email: [jianfeng@math.duke.edu](mailto:jianfeng@math.duke.edu).
- Matthew S. Zhang, Department of Mathematics, MIT. Email: [shuns436@mit.edu](mailto:shuns436@mit.edu).

## Feedback

Feedback on the theorem statements, proof details, oracle accounting, and exposition is welcome. Please identify the manuscript and the relevant section or equation when reporting a correction.
