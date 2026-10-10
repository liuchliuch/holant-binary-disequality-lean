import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Generators
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.API


namespace Holant.LocalDrafts.MainChain.TransformRecognition.PositiveCatalogueMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open ComplexIsolation.RootSearchDriver (cross)
open StructuralListMachine (exactLength)

abbrev Request := NegativeCatalogueMachine.Request
abbrev encoding := NegativeCatalogueMachine.encoding
abbrev degreeEncoding := NegativeCatalogueMachine.degreeEncoding
abbrev fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) : Request :=
  NegativeCatalogueMachine.fromSource target S h

abbrev Raw := List ℚ × (RationalBox × (List RationalPolynomialCode × List (List ℚ)))
abbrev rawLastEncoding := pairEncoding CommonFieldMachine.expressionsEncoding
  PositiveCertificateMachine.vectorsEncoding
abbrev rawTailEncoding := pairEncoding CommonFieldMachine.boxEncoding rawLastEncoding
abbrev rawEncoding := pairEncoding CommonFieldMachine.coordinatesEncoding rawTailEncoding
abbrev Payload := Raw × ComplexIsolation.Certificate
abbrev payloadEncoding := pairEncoding rawEncoding ComplexIsolation.CertificateMachine.certificateEncoding

def rawWire {m k d : ℕ}
    (a : PowerArithmetic.Vector d × (RationalBox ×
      ((Fin m → RationalPolynomialCode) × MatrixWitness.Candidate d k))) : Raw :=
  (List.ofFn a.1,a.2.1,List.ofFn a.2.2.1,List.ofFn (fun i => List.ofFn (a.2.2.2 i)))

def raw (m n d h : ℕ) : List Raw :=
  cross (NegativeCatalogueMachine.relations d h)
    (cross (StructuredCatalogue.boxes h)
      (cross (NegativeCatalogueMachine.expressions m h)
        (exactLength (NegativeCatalogueMachine.relations d h) n)))

def payloads (m n d h : ℕ) : List Payload :=
  cross (raw m n d h) (ComplexIsolation.RootSearchDriver.certificates h)

def load (r : Request) (d : ℕ) (p : Payload) : PositiveCertificateMachine.Request :=
  ⟨⟨d+1,p.1.1,p.1.2.1,p.1.2.2.1,r.targets⟩,r.equations,p.1.2.2.2,p.2⟩

def atDegree (r : Request) (d : ℕ) : List PositiveCertificateMachine.Request :=
  (payloads r.coefficients r.variables d r.height).map (load r d)

def catalogue (r : Request) : List PositiveCertificateMachine.Request :=
  (StructuredCatalogue.naturals r.height).flatMap (atDegree r)

theorem raw_eq (m k d h : ℕ) :
    raw m (5+k) d h = (StructuredCatalogue.rawAtDegree m k d h).map rawWire := by
  unfold raw NegativeCatalogueMachine.relations NegativeCatalogueMachine.expressions
  simp only [exactLength,NegativeCatalogueMachine.vectors_map,List.map_map,
    StructuredCatalogue.rawAtDegree,rawWire,cross,List.map_flatMap,List.flatMap_map,
    Function.comp_def]

theorem load_fromSource {m k d : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (a : PowerArithmetic.Vector d × (RationalBox ×
      ((Fin m → RationalPolynomialCode) × MatrixWitness.Candidate d k)))
    (c : ComplexIsolation.Certificate) :
    load (fromSource target S h) d (rawWire a,c) =
      PositiveCertificateMachine.fromSource target S (⟨d,a⟩,c) := rfl

theorem atDegree_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h d : ℕ) :
    atDegree (fromSource target S h) d =
      (cross (StructuredCatalogue.rawAtDegree m k d h)
        (ComplexIsolation.RootSearchDriver.certificates h)).map
          (fun p => PositiveCertificateMachine.fromSource target S (⟨d,p.1⟩,p.2)) := by
  unfold atDegree payloads
  change (cross (raw m (5+k) d h) _).map _ = _
  rw [raw_eq]
  simp only [cross,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  rfl

theorem catalogue_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    catalogue (fromSource target S h) =
      (StructuredCatalogue.positive m k h).map
        (PositiveCertificateMachine.fromSource target S) := by
  change (StructuredCatalogue.naturals h).flatMap (fun d => atDegree (fromSource target S h) d) = _
  simp_rw [atDegree_fromSource]
  simp only [StructuredCatalogue.positive,StructuredCatalogue.sigma,
    StructuredCatalogue.naturals,cross,List.flatMap_assoc,List.flatMap_map,
    List.map_flatMap,List.map_map,Function.comp_def]

theorem generated_shape {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (c : PositiveCertificateMachine.Request)
    (hc : c ∈ catalogue (fromSource target S h)) : c.shape=true := by
  rw [catalogue_fromSource] at hc
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hc
  exact PositiveCertificateMachine.fromSource_shape target S a

end Holant.LocalDrafts.MainChain.TransformRecognition.PositiveCatalogueMachine
