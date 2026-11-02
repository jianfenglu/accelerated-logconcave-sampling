# Markov semigroup proof provenance

Copyright Michael R. Douglas, 2026. Apache-2.0; see LICENSE and individual headers.
Upstream: https://github.com/mrdouglasny/markov-semigroups
Upstream revision: `acf649108ea2222f4a8544a2782f448cb502492a`.

This Gaussian OU subset was adapted through an intermediate project to the present
pinned Lean/mathlib versions. Internal imports were relocated; original declaration
namespaces and file notices are retained. The port includes a measurable-premise
correction to the low-level `integral_abs_eq_eLpNorm_one_toReal` helper and excludes
unused abstract axioms/wrappers from the earlier port. Historical source comments
are not claims of current verification; consult the top-level verification status.
