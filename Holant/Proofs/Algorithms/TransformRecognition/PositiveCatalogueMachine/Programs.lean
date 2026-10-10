import Holant.Proofs.Algorithms.TransformRecognition.PositiveCatalogueMachine.Catalogue


namespace Holant.LocalDrafts.MainChain.TransformRecognition.PositiveCatalogueMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

namespace Generation
noncomputable section

def values : Executes degreeEncoding
    (framedListEncoding PositiveCertificateMachine.vectorsEncoding)
    (fun p => StructuralListMachine.exactLength
      (NegativeCatalogueMachine.relations p.2 p.1.height) p.1.variables) :=
  NegativeCatalogueMachine.Programs.vectorLists CommonFieldMachine.coordinatesEncoding
    NegativeCatalogueMachine.Generation.relations
    (Executes.ofComputes (NegativeCatalogueMachine.Access.request.andThen
      NegativeCatalogueMachine.Access.variables))

def raw : Executes degreeEncoding (framedListEncoding rawEncoding)
    (fun p => PositiveCatalogueMachine.raw p.1.coefficients p.1.variables p.2 p.1.height) :=
  NegativeCatalogueMachine.Programs.cross CommonFieldMachine.coordinatesEncoding rawTailEncoding
    NegativeCatalogueMachine.Generation.relations
    (NegativeCatalogueMachine.Programs.cross CommonFieldMachine.boxEncoding rawLastEncoding
      (NegativeCatalogueMachine.Generation.height.comp NegativeCatalogueMachine.Programs.boxes)
      (NegativeCatalogueMachine.Programs.cross CommonFieldMachine.expressionsEncoding
        PositiveCertificateMachine.vectorsEncoding NegativeCatalogueMachine.Generation.expressions values))

def payloads : Executes degreeEncoding (framedListEncoding payloadEncoding)
    (fun p => PositiveCatalogueMachine.payloads p.1.coefficients p.1.variables p.2 p.1.height) :=
  NegativeCatalogueMachine.Programs.cross rawEncoding
    ComplexIsolation.CertificateMachine.certificateEncoding raw
    (NegativeCatalogueMachine.Generation.height.comp NegativeCatalogueMachine.Programs.certificates)

end
end Generation

namespace Loading
abbrev inputEncoding := pairEncoding degreeEncoding payloadEncoding

noncomputable def executes : Executes inputEncoding PositiveCertificateMachine.requestEncoding
    (fun p => load p.1.1 p.1.2 p.2) := by
  let rd := Wiring.firstComputes degreeEncoding payloadEncoding
  let r := rd.andThen NegativeCatalogueMachine.Access.request
  let p := Wiring.secondComputes degreeEncoding payloadEncoding
  let raw := p.andThen (Wiring.firstComputes rawEncoding
    ComplexIsolation.CertificateMachine.certificateEncoding)
  let cert := p.andThen (Wiring.secondComputes rawEncoding
    ComplexIsolation.CertificateMachine.certificateEncoding)
  let relation := raw.andThen (Wiring.firstComputes CommonFieldMachine.coordinatesEncoding rawTailEncoding)
  let tail := raw.andThen (Wiring.secondComputes CommonFieldMachine.coordinatesEncoding rawTailEncoding)
  let box := tail.andThen (Wiring.firstComputes CommonFieldMachine.boxEncoding rawLastEncoding)
  let last := tail.andThen (Wiring.secondComputes CommonFieldMachine.boxEncoding rawLastEncoding)
  let expr := last.andThen (Wiring.firstComputes CommonFieldMachine.expressionsEncoding
    PositiveCertificateMachine.vectorsEncoding)
  let vals := last.andThen (Wiring.secondComputes CommonFieldMachine.expressionsEncoding
    PositiveCertificateMachine.vectorsEncoding)
  let dimension := (Executes.ofComputes rd).comp NegativeCatalogueMachine.Generation.dimension
  let commonWire := Executes.pair dimension (Executes.ofComputes
    (pairComputes relation (pairComputes box
      (pairComputes expr (r.andThen NegativeCatalogueMachine.Access.targets)))))
  let common : Executes inputEncoding CommonFieldMachine.requestEncoding
      (fun p => ⟨p.1.2+1,p.2.1.1,p.2.1.2.1,p.2.1.2.2.1,p.1.1.targets⟩) :=
    Executes.recode commonWire id (fun _ => rfl) (fun _ => rfl)
  let loaded := Executes.pair common (Executes.ofComputes
    (pairComputes (r.andThen NegativeCatalogueMachine.Access.equations) (pairComputes vals cert)))
  exact Executes.recode loaded id (fun _ => rfl) (fun _ => rfl)

end Loading

namespace Generation
noncomputable section

def atDegree : Executes degreeEncoding (framedListEncoding PositiveCertificateMachine.requestEncoding)
    (fun p => PositiveCatalogueMachine.atDegree p.1 p.2) :=
  NegativeCertificateMachine.Lists.map degreeEncoding payloadEncoding PositiveCertificateMachine.requestEncoding
    payloads (fun rd p => load rd.1 rd.2 p) Loading.executes

def degrees : Executes encoding (framedListEncoding encodingNatBool)
    (fun r => StructuredCatalogue.naturals r.height) :=
  (Executes.ofComputes NegativeCatalogueMachine.Access.height).comp
    NegativeCatalogueMachine.Programs.naturals

def families : Executes encoding
    (framedListEncoding (framedListEncoding PositiveCertificateMachine.requestEncoding))
    (fun r => (StructuredCatalogue.naturals r.height).map (PositiveCatalogueMachine.atDegree r)) :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool
    (framedListEncoding PositiveCertificateMachine.requestEncoding) degrees
      PositiveCatalogueMachine.atDegree atDegree

def executes : Executes encoding (framedListEncoding PositiveCertificateMachine.requestEncoding) catalogue :=
  Executes.congr (families.comp
    (Executes.ofComputes (WireLists.flatten PositiveCertificateMachine.requestEncoding)))
      (fun r => by simp only [catalogue,List.flatMap_def])

def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    Turing.TM2OutputsInTime executes.machine.computer (encoding.encode (fromSource target S h))
      (some ((framedListEncoding PositiveCertificateMachine.requestEncoding).encode
        ((StructuredCatalogue.positive m k h).map (PositiveCertificateMachine.fromSource target S))))
      (executes.cost (fromSource target S h)) := by
  simpa only [catalogue_fromSource] using executes.outputs (fromSource target S h)

end
end Generation

end Holant.LocalDrafts.MainChain.TransformRecognition.PositiveCatalogueMachine
