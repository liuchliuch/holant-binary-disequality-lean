import Holant.Tractable.KPresentation

/-!
# Exact source correspondence and remaining obligations

Source: authoritative `paper1.tex`, rewritten 2026-09-27, subsection
`subsec:standard-classes` and definition `def:common-transformability`.
This module is documentation plus the public import of the implemented definitions.

* `AlgebraicComplex` is the intermediate subfield `algebraicClosure ℚ ℂ`.
  `imaginaryUnit` is literally complex `I`, and `sqrtTwo` is literally the
  positive real square root embedded in `ℂ`, both with integral certificates.
  `zetaEight = (1 + imaginaryUnit) / sqrtTwo` is the source's specified root;
  its square, fourth, and eighth powers are proved. No alternative root is chosen.
* `Affine` matches `eq:affine-class` (source lines 1896–1916). An `AffineSystem`
  carries the finite row count, `ZMod 2` matrix, and right-hand side. `Holds`
  is the literal row-by-row sum. `QuadraticPhase.eval` is the constant plus
  linear terms plus exactly the pairs `j < k`; `even_mixed` requires each
  contributing coefficient to be zero or two in `ZMod 4`. The exponent uses
  the canonical residue representative; `imaginaryUnit_pow_four` proves that
  choosing residues is compatible with the intended fourth-root phase.
* `Product` matches source lines 2073–2079. Its scale witness is nonzero, and
  its finite list consists only of nonzero unary functions, equality, and
  disequality on designated ports. List membership does not require different
  ports or factors. The empty list gives the constant scale; inconsistent
  products are actual zero functions. Zero is separately admitted in `Affine`
  and `Product`, without replacing nonzero scale hypotheses.
* `LocalAffine` matches source lines 2080–2091. `phaseMatrix` is the literal
  diagonal matrix `diag(1, zetaEight)`, and a Boolean support coordinate selects
  its zeroth or first power. `localTwist` uses the already-defined full ordered
  tensor-product `Signature.coordinateAction`. Its defining universal quantifier
  ranges over every assignment where the original signature is nonzero.
* `AtMostOneSupport` is the displayed support-weight definition of `𝓜`.
* `CommonTransformable` includes finiteness, the actual equality-edge pullback,
  and an outer two-sided invertible-kernel witness shared by all signatures.
  `KMatrix`, `KInverse`, and `sourceKBasis` fix the source's normalized matrix
  `K = (1/√2) [[1,1],[i,-i]]`. Both inverse products and `KᵀK=X` are proved.
  `CommonKPresentation` is `eq:common-K-presentation-predicate` in the original
  computational coordinates. `CommonKPresentationInKCoordinates` is the displayed
  condition for an input `Γ` already in `K` coordinates. The full equivalence
  between ordinary common transformability and original-coordinate K-presentation
  is proved in `commonTransformable_iff_commonKPresentation`.

All pairing and matrix operations are bilinear, with ordinary transpose and no
complex conjugation. Invertibility is represented by an explicit matrix, inverse,
and both inverse equations, rather than by a determinant predicate or an
uninterpreted type. The common-basis equivalence does not need scalar/permutation
closure assumptions; it is valid for arbitrary target classes.

## Scope limits

These definitions and elementary consequences do not prove tractability,
effective recognition, any complexity bound, the full affine phase criterion,
or the flat-Lagrangian and character-flat classifications. In particular, this
semantic algebraic-complex carrier is not an effective algebraic-number codec.
General port-permutation closure of `Affine` and `LocalAffine` is not asserted
here. The separate arithmetic and machine semantics developments retain their
own obligations; none is discharged merely by this semantic carrier.

`Tests/Tractable/Classes.lean` checks nonconstant affine linear/quadratic examples,
a genuine nonmember, repeated-variable products, actual nullary scalars, shared
identity presentation, and the mandatory edge even when the input family is empty.
-/
