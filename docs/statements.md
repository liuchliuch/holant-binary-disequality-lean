# Mathematical entry points

This guide refers to the November 6, 2026 Overleaf export recorded in
[`manuscript/source.json`](../manuscript/source.json). The bundled TeX is an
unmodified copy of `stoc2027-DEQ.tex`, including both the short submission and
its full paper. Full-paper numbers have the prefix `F.`. The correspondence
numbers below were checked against a fresh TeX build, rather than copied from
the October repository version.

The public Lean interface represents a finite family of algebraic
complex-valued Boolean signatures by a finite index set and an arity for each
index. Zero and nullary signatures remain in the evaluation input; the
tractability predicates delete them only for classification, exactly as in the
paper's preprocessing convention.

## Complexity and evaluation

The specifications are in [`Holant/Statements.lean`](../Holant/Statements.lean)
and their proofs are in [`Holant/Proofs.lean`](../Holant/Proofs.lean).

| Current manuscript | Specification | Proved theorem | Exact criterion |
| --- | --- | --- | --- |
| Theorem 1.1 / F.1.1, `thm:p1-deq2-dichotomy` | `Holant.Statements.BinaryDisequality` | `Holant.Theorems.binaryDisequality` | `ReTract(F union {X})` |
| Theorem 1.2 / F.1.2, `thm:p1-quaternary-kholant-dichotomy` | `Holant.Statements.Quaternary` | `Holant.Theorems.quaternary` | `ReTractX(F)` with native disequality edges |
| Theorem F.5.2, `thm:p1-eq2-kholant-dichotomy` | `Holant.Statements.EqualityAccessible` | `Holant.Theorems.equalityAccessible` | `ReTract(K F)`, with literal `I` in `F` |
| Theorem F.3.3, evaluation, `thm:predicate-algorithms` | `Holant.Statements.TractableEvaluation` | `Holant.Theorems.tractableEvaluation` | All seven clauses of `Tract(F)` |

The first theorem evaluates ordinary Holant with an added disequality vertex
label and equality edges. The other two dichotomies use native disequality
edges on the unchanged original family. The quaternary hypothesis includes
vanishing odd-weight entries, a nonzero endpoint product, and irreducibility
under arbitrary nonempty port partitions. It does not supply equality.
`TensorPrime` expresses the manuscript's irreducibility: a nonzero outer scalar
can be absorbed into one factor, and its `ports` equivalence permits arbitrary
input permutations.

`InFP` and `WitnessCountingHard` refer to the explicit graph and exact
coefficient encodings displayed in the specifications. Hardness quantifies over
counting problems with polynomial-time finite-machine verifiers. A common
basis is chosen for the whole family, including the edge condition; the
transformability branches never choose an independent basis for each signature.

## Genuine bridges from the earlier interfaces

The old proof implementations remain available, with their historical names.
The public theorems now use the new criteria through proved equivalences:

- [`STOC2027.lean`](../Holant/Tractable/STOC2027.lean) defines `ReTract` as the
  current name of the four existing structural cases and defines `ReTractX`
  directly using the native edge condition `U^T X U`. Its theorem
  `reTractX_iff_reTract_K` proves `ReTractX(F) iff ReTract(K F)` by substituting
  `M = K U`, transporting actual tensor factorizations, and commuting the same
  zero/nullary preprocessing with the invertible action.
- [`ReducedEdgeBridge.lean`](../Holant/Tractable/ReducedEdgeBridge.lean), using
  [`EdgeCriterionBridge.lean`](../Holant/Tractable/EdgeCriterionBridge.lean),
  proves the ordinary/disequality edge bridge used after Lemma F.5.1:
  `ReTract(F union {X}) iff ReTract(K (F union {I}))`. The proof uses the same
  whole-family witness, exact symmetric-binary inverse and sandwich identities,
  and class closure facts. It is not inferred from either complexity dichotomy.
- [`QuaternaryAnchor.lean`](../Holant/Tractable/QuaternaryAnchor.lean) proves
  `tract_iff_tractX_of_quaternary_endpoints`. Both nonzero endpoints exclude the
  one-sided and single-layer cases. A hypothetical product of matching factors
  has full support after inverse `K` or `KX`, contradicting an odd-weight zero.
  Thus `Tract(K F) iff ReTract(K F)` under the quaternary support assumptions.
  The bridge does not need primality; the public dichotomy retains primality.

The changed hardness branches use these same equivalences in the contrapositive
direction. No complexity separation assumption, extra tractability premise,
new axiom, or weakened conclusion is used. The old specification and proof
names `LiteralEquality` and `literalEquality` are compatibility aliases for the
new equality-accessible statement; the four Comparator targets use the current
public name `equalityAccessible`.

## Exact-input recognition

[`Holant/Decidability.lean`](../Holant/Decidability.lean) exports:

- `binaryDisequality_uniform`, deciding the direct `ReTract(F union {X})`
  criterion of Theorems 1.1/F.1.1;
- `equalityAccessible_uniform`, deciding `ReTract(K F)` for Theorem F.5.2;
- `quaternary_uniform`, deciding the native four-case `ReTractX(F)` criterion
  of Theorems 1.2/F.1.2;
- `uniform_source`, deciding the general seven-clause predicate of F.3.3.

Each result quantifies one machine before all finite layouts and exact
algebraic `RootCode` inputs, including explicit Boolean correctness and
execution bounds. The quaternary criterion recognizer is valid on all finite
inputs; the quaternary hypotheses are required for the complexity theorem,
not for running this recognizer. `literalEquality_uniform` remains a
compatibility alias. The older seven-clause quaternary recognizer remains in
its internal historical module, but is not the current public criterion.

These results assert decidability without a polynomial-time recognition claim.
They are included in the complete axiom audit and fresh-environment kernel
replay. The four configured Comparator checks target the complexity/evaluation
theorems above, not the recognition theorems.

## Structural results and historical corrections

[`Holant/Library.lean`](../Holant/Library.lean) imports the retained structural
lemmas and exact finite certificates. The new marked-group names preserve the
underlying matrices. [The structural correspondence review](structural-correspondence.md)
gives the new-to-old naming dictionary, current proof labels, and exact
supplementary coverage boundaries, including the newly explicit successor
diagram in Proposition F.5.18.

The current manuscript incorporates the historical corrections:

1. Equation (F.72), `eq:octahedral-mixed-mark-check`, uses
   `theta_dt(Q2 - Q3) = -sqrt(2) Q3` and
   `theta_td(Q1 - Q2) = sqrt(2) Q1`.
2. Lemma F.9.20, `lem:a4rel-sharp-stabilizer-line`, retains a common nonzero
   scalar normalization after the analytic unitary Clifford map. The new
   already-normalized clause is proved by the existing
   `StabilizerLine.normalized_sharp_support`.
3. Lemma F.9.21, `lem:a4rel-four-active-qubits`, retains that scalar in its proof
   and now describes the bound as at most four logical qubits.

The old October repository numbers were 9.18/9.19. The manuscript's acknowledgement
instead cites arXiv v1 numbers 9.19/9.20 and Equation (132); those references are
historical. Counterexample declarations in `SourceErrata` and
`no_clifford_sends_two_delta_to_delta` remain regression proofs for the earlier
errors, not assertions that the current manuscript contains those errors.
`python3 scripts/check_errata.py` checks the matrix identities independently
with exact rational coordinates in `Q(sqrt(2), i)`.

Comparator verifies the formal statements, their definitions, the permitted
axioms and kernel acceptance. It does not interpret the English paper or
certify a one-to-one mapping for every numbered auxiliary claim.
