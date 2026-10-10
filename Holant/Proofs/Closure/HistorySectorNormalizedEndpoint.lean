import Holant.Proofs.Closure.HistorySectorNormalizedEndpointAlgebra

/-! Actual source-backed endpoint dressing from the DERIVED complementary
support. All flip binaries are actual original-field representatives. The
nondegenerate endpoints refer to the SAME weighted sector graph; its inverse
physical return restores the literal dressed original-L source. No endpoint,
LP result, basis gadget or future compiler is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (sameBasis : params.basis = U)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (hcore : core.signature = ⟨4,q⟩)
variable (R : RootDeck G P torsion U N params sameBasis q)

def endpointWord : Word :=
  Classical.choose (complementary_pair G P U q torsion N params sameBasis core hcore R)

theorem endpointWord_pair :
    sectorCore G U q (endpointWord G P torsion U N params sameBasis q core hcore R) ≠ 0 ∧
    sectorCore G U q (complement (endpointWord G P torsion U N params sameBasis q core hcore R)) ≠ 0 :=
  Classical.choose_spec (complementary_pair G P U q torsion N params sameBasis core hcore R)

def endpointSource : Signature (OI.K G) 4 :=
  dress P.family torsion q (flipDelta G P torsion U N
    (endpointWord G P torsion U N params sameBasis q core hcore R))

def endpointDirect : DeckDirect P.family (endpointSource G P torsion U N params sameBasis q core hcore R) :=
  DeckDirect.ofRealizes P.equality (dress_actual P.family torsion q
    (Gadget.realizes_of_mem P.family .disequality q (by simpa only [hcore] using core.retained)) _)

def endpointGraph : Network Scalar 4 :=
  HistorySectorCardsNetworks.weighted G P U (endpointDirect G P torsion U N params sameBasis q core hcore R)

theorem endpointGraph_value :
    (endpointGraph G P torsion U N params sameBasis q core hcore R).denote =
      HistorySectorCards.dressed (algebraicEmbedding G) U P.family torsion (sectorCore G U q)
        (flipDelta G P torsion U N (endpointWord G P torsion U N params sameBasis q core hcore R)) :=
  (HistorySectorCardsNetworks.value G P U
    (endpointDirect G P torsion U N params sameBasis q core hcore R)).trans
      (HistorySectorCards.dress_transport (algebraicEmbedding G) U P.family torsion q _)

theorem endpointGraph_zero_nonzero :
    (endpointGraph G P torsion U N params sameBasis q core hcore R).denote (fun _ => false) ≠ 0 := by
  rw [endpointGraph_value]
  rw [(dressed_endpoints G P torsion U N (sectorCore G U q)
    (endpointWord G P torsion U N params sameBasis q core hcore R)).1]
  exact mul_ne_zero (flipWeight_nonzero _ (flipMultiplier_nonzero G P torsion U N) _)
    (endpointWord_pair G P torsion U N params sameBasis q core hcore R).1

theorem endpointGraph_one_nonzero :
    (endpointGraph G P torsion U N params sameBasis q core hcore R).denote (fun _ => true) ≠ 0 := by
  rw [endpointGraph_value]
  rw [(dressed_endpoints G P torsion U N (sectorCore G U q)
    (endpointWord G P torsion U N params sameBasis q core hcore R)).2]
  exact mul_ne_zero (flipWeight_nonzero _ (flipMultiplier_nonzero G P torsion U N) _)
    (endpointWord_pair G P torsion U N params sameBasis q core hcore R).2

theorem endpointGraph_edge (e : Fin (endpointGraph G P torsion U N params sameBasis q core hcore R).shape.edges) :
    (endpointGraph G P torsion U N params sameBasis q core hcore R).edge e = sectorEdge U :=
  HistorySectorCardsNetworks.edges G P U
    (endpointDirect G P torsion U N params sameBasis q core hcore R) e

def endpointReturn : HolographicOpenAccess G P U.symm
    (endpointGraph G P torsion U N params sameBasis q core hcore R) :=
  HistorySectorCardsNetworks.openReturn G P U
    (endpointDirect G P torsion U N params sameBasis q core hcore R)

theorem endpointReturn_original :
    (endpointReturn G P torsion U N params sameBasis q core hcore R).output =
      endpointSource G P torsion U N params sameBasis q core hcore R :=
  HistorySectorCardsNetworks.original_output G P U
    (endpointDirect G P torsion U N params sameBasis q core hcore R)

theorem endpointReturn_whole_graph :
    (endpointReturn G P torsion U N params sameBasis q core hcore R).restored =
      (endpointDirect G P torsion U N params sameBasis q core hcore R).network.map (algebraicEmbedding G) :=
  HistorySectorCardsNetworks.restored_exact G P U
    (endpointDirect G P torsion U N params sameBasis q core hcore R)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
