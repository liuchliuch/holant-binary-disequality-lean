import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Generators


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

namespace Loading
abbrev inputEncoding := pairEncoding degreeEncoding payloadEncoding

noncomputable def executes : Executes inputEncoding NegativeCertificateMachine.encoding
    (fun p => load p.1.1 p.1.2 p.2) := by
  let rd := Wiring.firstComputes degreeEncoding payloadEncoding
  let r := rd.andThen Access.request
  let p := Wiring.secondComputes degreeEncoding payloadEncoding
  let relation := p.andThen (Wiring.firstComputes CommonFieldMachine.coordinatesEncoding payloadCertEncoding)
  let tail := p.andThen (Wiring.secondComputes CommonFieldMachine.coordinatesEncoding payloadCertEncoding)
  let cert := tail.andThen (Wiring.firstComputes
    ComplexIsolation.CertificateMachine.certificateEncoding payloadBoxEncoding)
  let boxTail := tail.andThen (Wiring.secondComputes
    ComplexIsolation.CertificateMachine.certificateEncoding payloadBoxEncoding)
  let box := boxTail.andThen (Wiring.firstComputes CommonFieldMachine.boxEncoding payloadLastEncoding)
  let last := boxTail.andThen (Wiring.secondComputes CommonFieldMachine.boxEncoding payloadLastEncoding)
  let expr := last.andThen (Wiring.firstComputes CommonFieldMachine.expressionsEncoding
    NegativeCertificateMachine.multipliersEncoding)
  let mult := last.andThen (Wiring.secondComputes CommonFieldMachine.expressionsEncoding
    NegativeCertificateMachine.multipliersEncoding)
  let dimension := (Executes.ofComputes rd).comp Generation.dimension
  let commonWire := Executes.pair dimension (Executes.ofComputes
    (pairComputes relation (pairComputes box (pairComputes expr (r.andThen Access.targets)))))
  let common : Executes inputEncoding CommonFieldMachine.requestEncoding
      (fun p => ⟨p.1.2+1,p.2.1,p.2.2.2.1,p.2.2.2.2.1,p.1.1.targets⟩) :=
    Executes.recode commonWire id (fun _ => rfl) (fun _ => rfl)
  let loaded := Executes.pair (Executes.ofComputes (r.andThen Access.coefficients))
    (Executes.pair (Executes.ofComputes (r.andThen Access.variables))
      (Executes.pair common (Executes.ofComputes
        (pairComputes cert (pairComputes (r.andThen Access.equations) mult)))))
  exact Executes.recode loaded id (fun _ => rfl) (fun _ => rfl)

end Loading

namespace Generation
noncomputable section
def atDegree : Executes degreeEncoding (framedListEncoding NegativeCertificateMachine.encoding)
    (fun p => NegativeCatalogueMachine.atDegree p.1 p.2) :=
  NegativeCertificateMachine.Lists.map degreeEncoding payloadEncoding NegativeCertificateMachine.encoding
    payloads (fun rd p => load rd.1 rd.2 p) Loading.executes

def degrees : Executes encoding (framedListEncoding encodingNatBool)
    (fun r => StructuredCatalogue.naturals r.height) :=
  (Executes.ofComputes Access.height).comp Programs.naturals

def families : Executes encoding
    (framedListEncoding (framedListEncoding NegativeCertificateMachine.encoding))
    (fun r => (StructuredCatalogue.naturals r.height).map (NegativeCatalogueMachine.atDegree r)) :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool
    (framedListEncoding NegativeCertificateMachine.encoding) degrees
      NegativeCatalogueMachine.atDegree atDegree

def executes : Executes encoding (framedListEncoding NegativeCertificateMachine.encoding) catalogue :=
  Executes.congr (families.comp
    (Executes.ofComputes (WireLists.flatten NegativeCertificateMachine.encoding)))
      (fun r => by simp only [catalogue,List.flatMap_def])

noncomputable def source_outputs {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) :
    Turing.TM2OutputsInTime executes.machine.computer (encoding.encode (fromSource target S h))
      (some ((framedListEncoding NegativeCertificateMachine.encoding).encode
        ((StructuredCatalogue.negative m n S.length h).map
          (NegativeCertificateMachine.fromCandidate target S))))
      (executes.cost (fromSource target S h)) := by
  simpa only [catalogue_fromSource] using executes.outputs (fromSource target S h)
end
end Generation

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
