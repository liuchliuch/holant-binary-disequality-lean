# Structural correspondence for the STOC manuscript

This review concerns the November 6, 2026 Overleaf snapshot of
`stoc2027-DEQ.tex`, distributed as [`manuscript/paper.tex`](../manuscript/paper.tex).
Its SHA-256 is
`649a768c6b29681081e699f581e59d209aefc4e64fb0412ab8ad0b250a1383ab`.
The comparison baseline is this repository's October manuscript at commit
`ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711`. The full paper now follows the
short submission and uses the prefix `F.`. References below use both current
numbers and stable TeX labels; numbers were read from the rebuilt manuscript's
LaTeX auxiliary file.

The [public statement guide](statements.md) covers the complexity and
recognition interfaces. This document records the structural renaming,
retained proof implementations, historical corrections, and limits of the
supplementary correspondence review. Comparator checks its configured public
statements and their definition dependencies. It does not certify every
English claim in this document or every numbered claim in the manuscript.

## Terminology and marked coordinates

The new names distinguish the fixed transfer and reversal marks. They do not
license extra basis changes as gadgets. The retained Lean implementations
continue to distinguish analytic coordinates, actual binary representatives,
their nonzero scalars, and the transformed edge matrices.

| Current manuscript notation or terminology | Earlier notation | Lean representation |
| --- | --- | --- |
| Irreducible signature | Tensor-prime signature | `Prime` in `Holant/Proofs/FiniteGroups/Stabilization/FactorWorklist.lean`; local `TensorPrime` predicates in finite certificates |
| `D_(2m)^(Z)` | `M_m` | `Holant.Marked.groupM m`, `Parameters.M` |
| `D_(2m)^(Y)` | `B_m` | `Holant.Marked.groupB m`, `Parameters.B` |
| `D_(2m)^(X,1)` | `A_m` | `Holant.Marked.groupA m eta`, `Parameters.A`, with the same shifted-root condition |
| `D_(2m)^(X,0)` | `A_m^0` | `ClosureMarkedDihedralA0.NativeA0` and its constructed source normalization |
| `T^(int)` / `T^(ext)` | `T` / `T_ext` | The internal and external tetrahedral matrix and resource modules |
| `O^(dd)`, `O^(tt)`, `O^(dt)`, `O^(td)` | `O`, `O'`, `O_dt`, `O_td` | `OctahedralSeparator.Form` values `0`, `1`, `2`, `3`, respectively |
| `I^(0)` / `I^(1)` | The standard / opposite icosahedral displays | The standard icosahedral certificates and `Certificates.OppositeIcosahedral` |
| Logical qubits of a stabilizer code | Active qubits in a card cube | The common binary support subspace in `Platonic.ActiveSupport.Source` |

Lemma F.6.13 (`lem:marked-sector-dictionary`) retains the same exact matrix
calculation. [`Holant/Marked/Dictionary.lean`](../Holant/Marked/Dictionary.lean)
provides `Parameters.marked_sector_dictionary`, `edge_exact`,
`conjugates_group_onto`, and `actual_unique_lift`. In particular the transformed
edge multipliers are `1`, `-2i`, and `2`, with edge forms `X`, `I`, and
`diag(1,-eta^-1)`. The implementation preserves these scalars even where the
paper displays only a projective equality. Parameter `m` in the Lean dihedral
families is the rotation order; the displayed group order is `2m`.

Internal declaration names are retained where the mathematical statement is
unchanged. A rename of a section, a port as an input, or a tensor as a signature
does not require rebuilding a different mathematical argument.

## Corrections and the strengthened stabilizer statement

The new snapshot incorporates the two mathematical corrections already present
in the October repository manuscript. Its AI methodology paragraph cites the
original arXiv version's numbering. Those historical references must not be
read as the current full-paper numbers.

| Current claim | October repository reference | Established Lean entry |
| --- | --- | --- |
| Equation (F.72), `eq:octahedral-mixed-mark-check` | The mixed-mark calculation | `OctahedralSeparator.SourceErrata.dt_corrected_mark` and `td_corrected_mark` |
| Lemma F.9.20, `lem:a4rel-sharp-stabilizer-line` | Lemma 9.18 | `StabilizerLine.source_sharp_stabilizer_line` and `normalized_sharp_support` |
| Lemma F.9.21, `lem:a4rel-four-active-qubits` | Lemma 9.19 | `ActiveSupport.source_four_active_qubits`, `source_projective_four_active_qubits`, and `source_support_subset` |

The mixed-mark identities remain
`theta_dt(Q2 - Q3) = -sqrt(2) Q3` and
`theta_td(Q1 - Q2) = sqrt(2) Q1`.
The declarations containing `plus_actual` or `not_printed` are regression
certificates for the original incorrect plus-sign claims. They do not report
an error in the current manuscript. [`scripts/check_errata.py`](../scripts/check_errata.py)
also evaluates both corrected identities and both historical counterexamples
using rational coordinates in `Q(sqrt(2), i)`.

The sharp stabilizer-line lemma now states its already-normalized case
explicitly: when `u = delta`, the support alternative holds in the current
coordinates. The existing theorem
[`normalized_sharp_support`](../Holant/Platonic/StabilizerLine/Normalized.lean)
proves precisely that implication. Its `SharpSupport` conclusion is a singleton
away from zero or a binary linear subspace of dimension at most two. No
additional Clifford witness is required for that case. The general theorem
constructs a genuine unitary Clifford `C` and a nonzero scalar `alpha` with
`C u = alpha delta`. `SharpSupport.scale_iff` proves that dividing both images
by `alpha` leaves the support alternative unchanged.

The new proof writes the quadratic phase quotient's three-cube identity
explicitly. The existing normalized proof retains the same support-cardinality
and quadratic-phase argument. The four-logical-qubit proof then uses a single
common normalization and the double-incidence bound. Its rewording from twelve
test representatives to all kernels in those twelve projective classes is
covered by `source_projective_four_active_qubits`: the nonzero representative
scales are removed by linearity and affine scalar invariance. The conclusion
`source_support_subset` covers every binary input matrix, including matrices
outside the tested projective classes.

The norm obstruction
`StabilizerLine.no_clifford_sends_two_delta_to_delta` remains a useful
regression theorem: the required common amplitude normalization cannot be
absorbed into the definition of a unitary Clifford.

## Stabilizer, Radon, and finite-certificate proof organization

The expanded Hilbert-space and stabilizer conventions distinguish physical
operators, logical operators, encoders, decoders, and fixed ancillas. The
semantic interface in
[`Platonic/StabilizerErasure/SemanticFullSource.lean`](../Holant/Platonic/StabilizerErasure/SemanticFullSource.lean)
starts with `IsStabilizerIsometry`, rather than assuming a Clifford encoder as
an extra input. `source_semantic_stabilizer_erasure_column_normal_form` constructs
the needed code description. Its eigenvalue variant covers the arbitrary
fourth-root stabilizer character through a proved equivalence. The shortening
entry `source_stabilizer_code_tetrahedral_shortening` in
[`Platonic/StabilizerShortening/Source.lean`](../Holant/Platonic/StabilizerShortening/Source.lean)
keeps the selected actual contraction kernel separate from analytic Clifford
coordinates.

The character-flat arguments move into Appendix F.D. Their existing entry
points remain applicable:

| Current claim | Retained implementation |
| --- | --- |
| Lemma F.D.3, `lem:v4-signed-radon` | `ReedMuller.SignedRadon.source_signed_radon_fixed_graph`, `source_accessible_signed_radon`, and `source_signed_radon_choice_independence` |
| Lemma F.D.4, `lem:v4-character-two-chart` | `ReedMuller.TwoChart.source_character_two_chart_from_actual_networks` and `source_character_two_chart_gadget` |
| Lemma F.D.5, `lem:v4-affine-character-radon` | `ReedMuller.CharacterRecognition.source_affine_to_character_radon_even`, `source_character_from_actual_networks`, and `source_affine_to_character_algebraic` |

These statements keep the fixed graph, Bell-sign convention, actual nonzero
scalars, arity bounds, and exact algebraic input. The source proofs' shorter
descriptions of support integration and cycle shortening do not change the
transfer identities in `Dihedral.CompatibleClosure.Interface` or the finite
coefficient certificates imported by [`Holant/Library.lean`](../Holant/Library.lean).
This is a reviewed correspondence for the named entries, not an assertion of
an independently checked bijection with every numbered auxiliary claim.

## Statement-level revision inventory

The comparison of labeled theorem, lemma, proposition, corollary and definition
statements retained all 178 labels from the October source. Six newly labeled
statements are five short-paper restatements and Proposition F.5.18. This is a
source correspondence review, not a claim that every statement is an independent
Lean export. Beyond the changed public criteria, the generalized anchor, the
already-normalized stabilizer clause, and the new successor diagram, the
statement comparison found no additional change requiring a new public
hypothesis or a weakened conclusion.

Several large textual changes preserve the existing semantics:

| Current statement | Reviewed change |
| --- | --- |
| F.3.4, `lem:factor-saturation` | The factor worklist and decreasing potential move from the statement into its proof. |
| F.3.10, `lem:single-occurrence-replication` | The carrier-preserving context is expanded into its three boundary blocks, and ordinary/native edge cases are displayed separately. The single occurrence and nonzero closure requirements remain. |
| F.3.13, `cor:higher-equality-unary` | Equality and pinning accessibility are spelled out as Turing reductions, not direct gadget realizability. |
| F.5.10, `def:relative-stratum-protocol` | Completion is indexed by constructions, so distinct constructions may have equal output signatures. The noninjective key-to-card map in `FrozenQueue` and duplicate-preserving occurrence schedules already implement this distinction. |
| F.5.19, `def:effective-kernel-algebra` | The fixed transfer/kernel identification and Frobenius pairing are explicit; this supplies no new realizable linear combination. |
| F.6.30, `lem:nd-relative-reentry` | The standard-sector parameter and continuing local hypotheses are made explicit, as required by the existing relative-stability predicates. |
| F.A.6, `thm:cert-interface-affine-q4-odd` | Rank-one, infinite-order, and retained outputs are stated in the priority already used by the twelve-loop classification. |
| F.D.1, `lem:v4-character-flat-calculus` | The redundant phrase “zero or” is removed because `CFlat` already includes zero. |

The exotic Klein arity-eight certificate still requires all four cards to be
nonzero. The Platonic atlas counts and histograms are unchanged; differences in
some decimal table-column widths are layout changes, not certificate data.
Historical internal docstrings retain their original numbering; the current
numbering and correction map are centralized in this guide and the public
statement guide.

## General boundary representations

Appendix F.B (`app:general-boundaries`) relocates the old main-text general
half-edge convention. The main text now introduces ordinary dangling vertex
inputs first, while explicitly allowing isolated edge boxes. The partition
function and replacement tensor are unchanged.

[`Holant/OpenNetwork.lean`](../Holant/OpenNetwork.lean) retains the general
representation: `raw` is the half-edge assignment sum; `boundaryKernel` is the
incident `I` or `X` at a free endpoint and identity at an ordinary endpoint;
`tensor` applies the boundary correction. `tensor_eq_raw_of_ordinary` and
[`Network.tensor_asOpen`](../Holant/NetworkAsGadget.lean) identify the ordinary
model. [`OpenNetwork.tensor_edgeBox`](../Holant/EdgeBox.lean) proves that an
isolated edge contributes its kernel once, and `close_native_edgeBox` proves
the scalar `2` when an isolated native edge closes.

For native disequality edges, the general gluing proof covers all endpoint
cases. `ProjectiveContraction.Normalize.network_tensor` removes a free-to-vertex
wire without changing the tensor;
`ProjectiveContraction.Wire.circle_tensor` preserves the closed-wire factor
`2`; and `realizesUpTo_contract` and `realizesUpTo_network` provide contraction
and substitution with their nonzero scalars retained. The separate
`OrdinaryNormalization.openNetwork_exists_ordinary` conversion uses a supplied
literal equality vertex. That hypothesis belongs to that implementation and
must not be silently attached to the manuscript's local free-stub cancellation
identity.

[`Holant/ChargeConservation.lean`](../Holant/ChargeConservation.lean) proves the
closed native-X charge identity, including loops, parallel edges, nullary
vertices, and disconnected components. In particular,
`sum_charge_eq_zero_of_native_term` and
`denote_centralRestriction_of_common_side` support the closed-instance
arguments. The more general pointwise open-boundary charge formula printed in
Appendix F.B.2 is not exported as a separate theorem in this library. The
closed theorem must not be represented as a proof of that stronger open formula.

## Newly explicit successor diagram and coverage boundary

Proposition F.5.18 (`prop:finite-marked-successor-routing`) and Figure F.1
(`fig:complete-group-growth`) are new explicitly stated supplementary material.
They enumerate the marked types reachable under strict inclusion of complete
transfer groups, including twenty displayed arrows and suppressed divisibility
steps. The proposition concerns the complete realizable group after a restart;
it does not identify that group with the subgroup generated by the first new
binary.

The existing library proves the ingredients used by the dichotomy:

- `completeGroup_mono`, `completeGroup_lt_of_new_class`, and
  `groupDefect_lt_of_strict` in
  [`Stabilization/ActualGroups.lean`](../Holant/Proofs/FiniteGroups/Stabilization/ActualGroups.lean)
  concern the actual complete group and its bounded descent measure.
- `Node.step_decreases` and `Node.no_infinite_continuation` in
  [`Stabilization/Termination.lean`](../Holant/Proofs/FiniteGroups/Stabilization/Termination.lean)
  justify restart termination without a successor graph oracle.
- `finite_subgroup_classification`, `finite_projective_group_facts`, and the
  literal model inclusions provide finite projective-group facts.
- [`ClosureMarkedSourceRouting.produce`](../Holant/Proofs/Closure/ClosureMarkedSourceRouting.lean)
  constructs the current marked branch from the actual residual-torsion family
  and retained equality.

There is no separate Lean directed-path specification or exhaustive theorem for
the new twenty-arrow figure in the existing library. The named ingredients and
the proved dichotomy therefore do not constitute a formal proof of Proposition
F.5.18 as stated. This supplementary diagram is outside the four public
Comparator targets; its remaining formalization scope is recorded here
explicitly. Its use as an explanatory diagram does not add a hypothesis to the
existing classification or termination proofs.
