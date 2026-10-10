import Holant.Proofs.Closure.ClosurePhysicalBridgeNetwork

/-! Concrete EqualityQuaternary boundary outputs. The exact certificate graph,
copy count and source clauses are saved as DATA, and its native mapped-current
vertices are descended to the original field and physically compiled. The input
family here is literal mapFamily of P.family; a row-normalized familyAction
with transformed edges requires a separate inverse network-transport proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.EightVertex.ProductAnchor (EndpointEven)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : Signature Scalar 4) (group : Set Mat)
variable (certificate : BoundaryCertificate (RH.mapFamily (algebraicEmbedding G) P.family) q group)

/-- This is the count in the actual certificate, not a fresh optimal count. -/
def certificateCopies : ℕ := Classical.choose certificate

theorem certificateCopies_bound : certificateCopies G P q group certificate ≤ 2 :=
  (Classical.choose_spec certificate).1

def certificateExit : ExactExit (RH.mapFamily (algebraicEmbedding G) P.family) q group
    (certificateCopies G P q group certificate) := (Classical.choose_spec certificate).2

/-- Literal chosen witness identity is retained before any coefficient descent. -/
def certificateNetwork : Network Scalar 4 :=
  Classical.choose (certificateExit G P q group certificate)

theorem certificateNetwork_clauses :
    Boundary.CoreLabels q (certificateNetwork G P q group certificate) ∧
    Boundary.Native (certificateNetwork G P q group certificate) ∧
    Counted.copies (certificateNetwork G P q group certificate) = certificateCopies G P q group certificate ∧
    EndpointEven (certificateNetwork G P q group certificate).denote ∧
    ¬GroupMatching group (certificateNetwork G P q group certificate).denote ∧
    Gadget.Realizes (RH.mapFamily (algebraicEmbedding G) P.family) .disequality
      (certificateNetwork G P q group certificate).denote ∧
    Boundary.Uses (RH.mapFamily (algebraicEmbedding G) P.family)
      (certificateNetwork G P q group certificate) :=
  Classical.choose_spec (certificateExit G P q group certificate)

structure BoundaryAccess where
  copies : ℕ
  copiesIdentity : copies = certificateCopies G P q group certificate
  copiesBound : copies ≤ 2
  graph : Network Scalar 4
  graphIdentity : graph = certificateNetwork G P q group certificate
  coreLabels : Boundary.CoreLabels q graph
  native : Boundary.Native graph
  counted : Counted.copies graph = copies
  endpointEven : EndpointEven graph.denote
  outsideGroupMatching : ¬GroupMatching group graph.denote
  actual : Gadget.Realizes (RH.mapFamily (algebraicEmbedding G) P.family) .disequality graph.denote
  uses : Boundary.Uses (RH.mapFamily (algebraicEmbedding G) P.family) graph
  access : NetworkGraphAccess G P (algebraicEmbedding G) graph uses
  accessIdentity : access = fromNetwork G P (algebraicEmbedding G) graph uses native

/-- A source BoundaryCertificate is consumed concretely. No desired output
preimage, source-field scalar, minimum-core hypothesis or compiler is supplied. -/
def fromBoundary : BoundaryAccess G P q group certificate := by
  let N := certificateNetwork G P q group certificate
  have h := certificateNetwork_clauses G P q group certificate
  exact ⟨certificateCopies G P q group certificate,rfl,
    certificateCopies_bound G P q group certificate,N,rfl,h.1,h.2.1,h.2.2.1,
    h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2,
    fromNetwork G P (algebraicEmbedding G) N h.2.2.2.2.2.2 h.2.1,rfl⟩

abbrev BoundaryAccess.output (d : BoundaryAccess G P q group certificate) := d.access.output
abbrev BoundaryAccess.toOriginal (d : BoundaryAccess G P q group certificate) := d.access.toOriginal
abbrev BoundaryAccess.fromOriginal (d : BoundaryAccess G P q group certificate) := d.access.fromOriginal

/-- The descended table is the output of the SAME certificate graph. -/
theorem BoundaryAccess.mappedOutput (d : BoundaryAccess G P q group certificate) :
    RH.mapSignature (algebraicEmbedding G) d.output = d.graph.denote := d.access.mappedOutput

/-- Full graph identity keeps loops, parallel edges, port order and scalar
components, even though the physically compiled ordinary macro is separately
constructed and charged by the real factor-access compiler. -/
theorem BoundaryAccess.mappedNetwork (d : BoundaryAccess G P q group certificate) :
    d.access.source.map (algebraicEmbedding G) = d.graph := d.access.mappedNetwork

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
