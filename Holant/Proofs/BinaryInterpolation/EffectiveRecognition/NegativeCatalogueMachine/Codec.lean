import Holant.Proofs.Algorithms.TransformRecognition.StructuralListMachine
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Resources


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic

structure Request where
  coefficients : ℕ
  «variables» : ℕ
  targets : List RootCode
  equations : NegativeCertificateMachine.System
  height : ℕ

abbrev RequestWire := ℕ × (ℕ × (List RootCode × (NegativeCertificateMachine.System × ℕ)))
abbrev lastEncoding := pairEncoding NegativeCertificateMachine.systemEncoding encodingNatBool
abbrev contextEncoding := pairEncoding CommonFieldMachine.rootsEncoding lastEncoding
abbrev tailEncoding := pairEncoding encodingNatBool contextEncoding
abbrev wireEncoding := pairEncoding encodingNatBool tailEncoding
def Request.wire (r : Request) : RequestWire :=
  (r.coefficients,r.variables,r.targets,r.equations,r.height)
def Request.unwire (w : RequestWire) : Request := ⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2⟩
def encoding : Encoding Request Bool where
  encode r := wireEncoding.encode r.wire
  decode w := (wireEncoding.decode w).map Request.unwire
  decode_encode r := by
    change (wireEncoding.decode (wireEncoding.encode r.wire)).map Request.unwire = some r
    rw [wireEncoding.decode_encode]
    cases r
    rfl

def fromSource {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) : Request :=
  ⟨m,n,List.ofFn target,NegativeCertificateMachine.systemWire S,h⟩

abbrev Payload := List ℚ × (ComplexIsolation.Certificate ×
  (RationalBox × (List RationalPolynomialCode × List NegativeCertificateMachine.Poly)))
abbrev payloadLastEncoding := pairEncoding CommonFieldMachine.expressionsEncoding
  NegativeCertificateMachine.multipliersEncoding
abbrev payloadBoxEncoding := pairEncoding CommonFieldMachine.boxEncoding payloadLastEncoding
abbrev payloadCertEncoding := pairEncoding ComplexIsolation.CertificateMachine.certificateEncoding
  payloadBoxEncoding
abbrev payloadEncoding := pairEncoding CommonFieldMachine.coordinatesEncoding payloadCertEncoding
abbrev degreeEncoding := pairEncoding encoding encodingNatBool

def payloadWire {m n q d : ℕ} (c : NullstellensatzSearch.Data m n q d) : Payload :=
  (List.ofFn c.relation,c.certificate,c.source,List.ofFn c.expression,
    List.ofFn (fun i => NegativeCertificateMachine.polyWire (c.multiplier i)))

def load (r : Request) (d : ℕ) (p : Payload) : NegativeCertificateMachine.Input :=
  ⟨r.coefficients,r.variables,
    ⟨d+1,p.1,p.2.2.1,p.2.2.2.1,r.targets⟩,
    p.2.1,r.equations,p.2.2.2.2⟩

theorem load_fromSource {m n d : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (h : ℕ) (c : NullstellensatzSearch.Data m n S.length d) :
    load (fromSource target S h) d (payloadWire c) =
      NegativeCertificateMachine.fromCandidate target S ⟨d,c⟩ := rfl

theorem load_targets (r : Request) (d : ℕ) (p : Payload) :
    (load r d p).field.targets=r.targets := rfl
theorem load_equations (r : Request) (d : ℕ) (p : Payload) :
    (load r d p).equations=r.equations := rfl
theorem load_multipliers (r : Request) (d : ℕ) (p : Payload) :
    (load r d p).multipliers=p.2.2.2.2 := rfl

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
