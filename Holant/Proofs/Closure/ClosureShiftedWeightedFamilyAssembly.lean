import Holant.Proofs.Closure.ClosureShiftedWeightedFamily

/-! Internally assembled literal standard-root sample family at the SAME saved
source anchor. Pairing alignment and pairwise factor-line distance are proved
from actual source stability. Shared zero-safe assembly supplies its genuine
2+(n-2) split, retaining the selected fixed-edge ports and unit multiplier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.TwoCardLocalization
open ClosurePhysicalBridge ClosureCompatibleAlignment
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (A : SourceAnchor G P torsion U N params f order)
variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (large : 2 ≤ r)
variable (i : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large)
variable (S : CurrentSelection G P torsion U N params f order A sameBasis nonstandard stable large i)

theorem selectionEdgeCount : S.native.edges = r+1 := by
  have h := Fintype.card_congr S.native.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

def selectionPorts : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr (selectionEdgeCount G P torsion U N params f order A sameBasis nonstandard stable large i S)).symm
    (Equiv.refl Bool)).trans S.native.ports

def selectionTables (e : Fin (r+1)) : Mat :=
  (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).matrix
    ((finCongr (selectionEdgeCount G P torsion U N params f order A sameBasis nonstandard stable large i S)).symm e)

theorem selectionProduct : Signature.contract (M i.val.1 i.val.2.val)
    (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large) =
    Holant.Certificates.MatchingContractionClosure.productValue
      (selectionPorts G P torsion U N params f order A sameBasis nonstandard stable large i S)
      (selectionTables G P torsion U N params f order A sameBasis nonstandard stable large i S)
      (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).scalar := by
  rw [selectionCoordinate_equation]
  funext x
  apply congrArg ((selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).scalar * ·)
  exact (Equiv.prod_comp
    (finCongr (selectionEdgeCount G P torsion U N params f order A sameBasis nonstandard stable large i S)).symm
    (fun e => (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).matrix e
      (x (S.native.ports (e,false))) (x (S.native.ports (e,true))))).symm

theorem selectionPairing : (Pairing.ofPorts (anchorPorts G P torsion U N params f order A)).mate =
    (Pairing.ofPorts (selectionPorts G P torsion U N params f order A sameBasis nonstandard stable large i S)).mate := by
  have source := source_pairing_same G P torsion U N f stable order (by omega) ⟨r+1,by omega⟩
    A.parity i.val.1 A.phase (inversePhase G P torsion U N i.val.1 i.val.2)
    A.native S.native A.valid S.valid A.scalar_nonzero S.scalar_nonzero A.sourceEquation S.literal
  funext u
  have h := congrArg (fun mate : Equiv.Perm (Fin (2*r+2)) => mate u) source
  change A.native.ports ((A.native.ports.symm u).1,!(A.native.ports.symm u).2) =
    S.native.ports ((S.native.ports.symm u).1,!(S.native.ports.symm u).2) at h
  simpa [Pairing.ofPorts,anchorPorts,selectionPorts] using h

def alignedTables : Fin (r+1) → Mat :=
  alignedFactor (anchorPorts G P torsion U N params f order A)
    (selectionPorts G P torsion U N params f order A sameBasis nonstandard stable large i S)
    (selectionTables G P torsion U N params f order A sameBasis nonstandard stable large i S)

theorem alignedTables_member (e : Fin (r+1)) :
    alignedTables G P torsion U N params f order A sameBasis nonstandard stable large i S e ∈ groupM N.m :=
  alignedFactor_group (by have := N.range; omega) _ _ _
    (fun e => selectionCoordinate_member G P torsion U N params f order A sameBasis nonstandard stable large i S _) e

theorem alignedProduct : Signature.contract (M i.val.1 i.val.2.val)
    (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large) =
    Holant.Certificates.MatchingContractionClosure.productValue
      (anchorPorts G P torsion U N params f order A)
      (alignedTables G P torsion U N params f order A sameBasis nonstandard stable large i S)
      (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i S).scalar := by
  rw [selectionProduct]
  exact (aligned_product _ _ (selectionPairing G P torsion U N params f order A sameBasis nonstandard stable large i S) _ _).symm

def currentFamilyTables (i : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large) :
    Fin (r+1) → Mat := alignedTables G P torsion U N params f order A sameBasis nonstandard stable large i
      (selectSample G P torsion U N params f order A sameBasis nonstandard stable large i)

def currentFamilyCoefficient (i : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large) : Scalar :=
  (selectionCoordinate G P torsion U N params f order A sameBasis nonstandard stable large i
    (selectSample G P torsion U N params f order A sameBasis nonstandard stable large i)).scalar

/-- Real selected samples and actual outside CURRENT products produce the line
bound; no factor distance, outside group membership or successful split is input. -/
theorem currentFamily_distance
    (i j : CurrentSample G P torsion U N params f order A sameBasis nonstandard stable large)
    (e d : Fin (r+1)) (different : e≠d) :
    ProjectivelyEqual (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large j e)
      (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large i e) ∨
    ProjectivelyEqual (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large j d)
      (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large i d) := by
  exact one_step_unrestricted_bound N.range large
    (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large)
    (M i.val.1 i.val.2.val) (M j.val.1 j.val.2.val) (anchorPorts G P torsion U N params f order A)
    (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large i)
    (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large j)
    (currentFamilyCoefficient G P torsion U N params f order A sameBasis nonstandard stable large i)
    (currentFamilyCoefficient G P torsion U N params f order A sameBasis nonstandard stable large j)
    (fun e => alignedTables_member G P torsion U N params f order A sameBasis nonstandard stable large i _ e)
    (fun e => alignedTables_member G P torsion U N params f order A sameBasis nonstandard stable large j _ e)
    (selectionCoordinate_scalar G P torsion U N params f order A sameBasis nonstandard stable large i _)
    (selectionCoordinate_scalar G P torsion U N params f order A sameBasis nonstandard stable large j _)
    (alignedProduct G P torsion U N params f order A sameBasis nonstandard stable large i _)
    (alignedProduct G P torsion U N params f order A sameBasis nonstandard stable large j _)
    (fun e γ t => anchored_delete_product G P torsion U N params f order A sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ e γ t)
    (fun e j different γ t => anchored_splice_product G P torsion U N params f order A sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ e j different γ t)
    e d different

def assembledFamily : ClosureBStableFactor.Family N.m r
    (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large) where
  anchor := savedSample G P torsion U N params f order A sameBasis nonstandard stable large
  ports := anchorPorts G P torsion U N params f order A
  tables := currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
  coefficient := currentFamilyCoefficient G P torsion U N params f order A sameBasis nonstandard stable large
  equation i := alignedProduct G P torsion U N params f order A sameBasis nonstandard stable large i _
  distance := currentFamily_distance G P torsion U N params f order A sameBasis nonstandard stable large

/-- Actual same anchored/gauged ancestor split, with the retained fixed-edge
partition and literal unit multiplier. Original-field descent follows separately. -/
theorem currentStandard_split :
    ∃ e : Fin (r+1),∃ R : Signature Scalar (2*r+2),∃ S : ProperSplit
      (⟨2*r+4,currentStandard G P torsion U N params f order A sameBasis nonstandard stable large⟩ : AnySignature Scalar)
      ⟨2,kernelSignature (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
        (savedSample G P torsion U N params f order A sameBasis nonstandard stable large) e)⟩ ⟨2*r+2,R⟩,
      S.ports = (factorPorts (2*r)).trans (ClosureStableFactor.liftResidual
        ((assembledFamily G P torsion U N params f order A sameBasis nonstandard stable large).residualOrder e)) ∧ S.scale = 1 := by
  exact (assembledFamily G P torsion U N params f order A sameBasis nonstandard stable large).split N.range large

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
