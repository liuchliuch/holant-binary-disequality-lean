# Mathematical entry points

The manuscript uses finite families of algebraic complex-valued Boolean
signatures. The public Lean interface represents a family by a finite index
set and an arity for each index. Zero and nullary signatures remain part of
the original family.

## Complexity and evaluation

The propositions are in [`Holant/Statements.lean`](../Holant/Statements.lean).
Their proofs are in [`Holant/Proofs.lean`](../Holant/Proofs.lean).

| Manuscript | Specification | Proved theorem | Criterion |
| --- | --- | --- | --- |
| Theorem 1.1 | `Holant.Statements.BinaryDisequality` | `Holant.Theorems.binaryDisequality` | `TractX(K(F union {I}))` |
| Theorem 1.2 | `Holant.Statements.LiteralEquality` | `Holant.Theorems.literalEquality` | `TractX(K(F))`, with literal `I` in `F` |
| Theorem 1.3 | `Holant.Statements.Quaternary` | `Holant.Theorems.quaternary` | `Tract(K(F))`, with the stated quaternary member |
| Theorem 2.19, evaluation | `Holant.Statements.TractableEvaluation` | `Holant.Theorems.tractableEvaluation` | All seven clauses of `Tract(F)` |

The first theorem evaluates ordinary Holant with an added disequality vertex
label and equality edges. The second and third use native disequality edges
on the unchanged original family. The quaternary hypothesis includes even
support, nonzero endpoint product, and tensor primality under arbitrary port
partitions. It does not supply an extra equality signature.

`InFP` and `WitnessCountingHard` refer to the explicit graph and coefficient
encodings displayed in the specifications. Hardness quantifies over counting
problems with polynomial-time finite-machine verifiers. A common basis or
phase witness is chosen for the whole family, not independently for each row.

## Exact-input recognition

[`Holant/Decidability.lean`](../Holant/Decidability.lean) exports:

- `binaryDisequality_uniform`: recognition for Theorem 1.1;
- `literalEquality_uniform`: recognition for Theorem 1.2;
- `quaternary_uniform`: recognition for Theorem 1.3;
- `uniform_source`: the general seven-clause recognition in Theorem 2.19.

Each result puts one machine before all finite input layouts. Inputs contain
exact algebraic root descriptors. The actual output encodings and execution
witnesses appear in the underlying declarations. These results assert
termination and correctness, without a polynomial-time recognition bound.
They are included in the library's axiom audit and kernel replay; the current
Comparator configuration targets the four complexity/evaluation theorems above.

## Supplementary results

[`Holant/Library.lean`](../Holant/Library.lean) imports the retained structural
lemmas and exact finite certificates. They cover the cyclic, dihedral,
Reed-Muller, Klein-four and Platonic arguments, along with graph and encoding
constructions used by the reductions. Finite certificates are proved in Lean;
no external Python calculation is admitted as an axiom.

## Corrections included in the manuscript

The supplied manuscript includes these mathematical corrections to the
September 27 source:

1. In the octahedral mixed-mark calculation, the required identities are
   `theta_dt(Q2 - Q3) = -sqrt(2) Q3` and
   `theta_td(Q1 - Q2) = sqrt(2) Q1`. The original plus-sign left sides both
   evaluate to `sqrt(2) Q2`.
2. Lemma 9.18 requires a common nonzero scalar normalization after a unitary
   Clifford transformation. First obtain `C u = alpha delta`, then multiply
   both tensors by `alpha^-1`. A unitary Clifford alone cannot send `2 delta`
   to a unit delta because it preserves the norm.
3. The proof of Lemma 9.19 keeps this scalar or uses the commonly normalized
   image. Nonzero scalar multiplication preserves support, so its conclusion
   is unchanged.

The corresponding Lean certificates are
`Holant.Certificates.OctahedralSeparator.SourceErrata`,
`Holant.Platonic.StabilizerLine.source_sharp_stabilizer_line`,
`Holant.Platonic.StabilizerLine.no_clifford_sends_two_delta_to_delta`, and
`Holant.Platonic.ActiveSupport.source_four_active_qubits`.
`python3 scripts/check_errata.py` also checks the matrix identities with exact
rational coordinates in `Q(sqrt(2), i)`.

Comparator verifies the identity of formal statements and their definitions.
It does not interpret the English paper or automatically certify a separate
one-to-one mapping for all numbered manuscript claims.
