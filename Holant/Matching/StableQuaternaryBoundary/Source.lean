import Holant.Matching.StableQuaternaryBoundary.PhysicalDeck

/-! Source Theorem 5.18 (`thm:equality-q4-boundary`).

The stable-state assumption is used through its literal retained resources,
tensor primality and complete physical matching deck. The theorem below proves
the boundary conclusion from these clauses alone. Finiteness, minimum arity,
factor saturation and completeness of the recomputed safe group are not needed
for this construction, so no substitute global `Stable` predicate is introduced.
The original q and the caller's coordinates remain fixed throughout. -/
noncomputable section
namespace Holant.Matching.StableQuaternaryBoundary
open Holant Holant.Marked Holant.Tractable
open Holant.Certificates.EqualityQuaternary
open Holant.EightVertex.ProductAnchor (EndpointEven)
set_option backward.isDefEq.respectTransparency false

/-- The entire A.8 interface follows from the full source deck, without
assuming a normalized support class, an output tensor, or a realization. -/
theorem source_stable_quaternary_interface (F : SignatureFamily Scalar)
    (row : SourceRow) (hrow : row.Valid) (reps : SourceRepresentatives F row)
    (hret : SourceRetained row reps) (q : Signature Scalar 4)
    (hp : TensorPrime q) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : MatchingDeck row reps q) :
    BoundaryCertificate F q (SourceGroup row) ∧ SourceDetail F q row reps :=
  source_equality_accessible_quaternary_interface F row hrow reps hret q hp hq hI
    (sourceDeck_of_matchingDeck row hrow reps q hd)

/-- Theorem 5.18: an actual native-X gadget over the same retained family,
using at most two vertices labelled by the exact original q, has an
endpoint-nondegenerate eight-vertex signature outside the current matching class.
The other vertices are binary resources in F, with their actual scalars. -/
theorem source_stable_quaternary_boundary (F : SignatureFamily Scalar)
    (row : SourceRow) (hrow : row.Valid) (reps : SourceRepresentatives F row)
    (hret : SourceRetained row reps) (q : Signature Scalar 4)
    (hp : TensorPrime q) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : MatchingDeck row reps q) :
    ∃ N : Network Scalar 4, Boundary.CoreLabels q N ∧ Boundary.Native N ∧
      Counted.copies N≤2 ∧ Boundary.Uses F N ∧ EndpointEven N.denote ∧
      ¬GroupMatching (SourceGroup row) N.denote ∧ Gadget.Realizes F .disequality N.denote := by
  obtain ⟨n,hn,N,hLabels,hNative,hCount,hEndpoint,hNonmatching,hActual,hUses⟩ :=
    (source_stable_quaternary_interface F row hrow reps hret q hp hq hI hd).1
  exact ⟨N,hLabels,hNative,by omega,hUses,hEndpoint,hNonmatching,hActual⟩

/-- Named-current-group form of the same statement. This is equality in the
original physical coordinates, not conjugacy to a listed group. -/
theorem source_stable_quaternary_boundary_of_group (F : SignatureFamily Scalar)
    (G : Set Mat) (row : SourceRow) (hG : G=SourceGroup row) (hrow : row.Valid)
    (reps : SourceRepresentatives F row) (hret : SourceRetained row reps)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : MatchingDeck row reps q) :
    ∃ N : Network Scalar 4, Boundary.CoreLabels q N ∧ Boundary.Native N ∧
      Counted.copies N≤2 ∧ Boundary.Uses F N ∧ EndpointEven N.denote ∧
      ¬GroupMatching G N.denote ∧ Gadget.Realizes F .disequality N.denote := by
  subst G
  exact source_stable_quaternary_boundary F row hrow reps hret q hp hq hI hd

/-- The primality clause used immediately after Theorem 5.18: all non-C2
rows and the C2 one-copy branch have a prime one-original-q exit. -/
theorem source_stable_quaternary_prime_exit (F : SignatureFamily Scalar)
    (row : SourceRow) (hrow : row.Valid) (reps : SourceRepresentatives F row)
    (hret : SourceRetained row reps) (q : Signature Scalar 4)
    (hp : TensorPrime q) (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : MatchingDeck row reps q) (hc2 : row=.c2 → C2.OneCopyCase q) :
    PrimeExit F q (SourceGroup row) := by
  have h := (source_stable_quaternary_interface F row hrow reps hret q hp hq hI hd).2
  cases row with
  | c2 => exact (h.1 (hc2 rfl)).prime
  | monomial _ => exact h.2.prime
  | standardKlein => exact h.prime
  | exoticKlein => exact h.prime

/-- The exceptional C2 alternative retains the actual two-original-q
network and its derived mixed-block normalization. -/
theorem source_stable_c2_mixed_exit (F : SignatureFamily Scalar)
    (reps : C2.Representatives F) (hret : SourceRetained .c2 reps)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : MatchingDeck .c2 reps q) (hm : ¬C2.OneCopyCase q) : MixedChoiceExit F q :=
  (source_stable_quaternary_interface F .c2 trivial reps hret q hp hq hI hd).2.2 hm

end Holant.Matching.StableQuaternaryBoundary
