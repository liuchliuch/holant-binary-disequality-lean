import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Resources
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Check
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.API


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (coordinatesEncoding)

abbrev Exponent := List ℕ
abbrev Term := Exponent × List ℚ
abbrev Poly := List Term
abbrev SourceTerm := ℕ × Exponent
abbrev Equation := List SourceTerm
abbrev System := List Equation
abbrev exponentEncoding := framedListEncoding encodingNatBool
abbrev termEncoding := pairEncoding exponentEncoding coordinatesEncoding
abbrev polyEncoding := framedListEncoding termEncoding
abbrev sourceTermEncoding := pairEncoding encodingNatBool exponentEncoding
abbrev equationEncoding := framedListEncoding sourceTermEncoding
abbrev systemEncoding := framedListEncoding equationEncoding
abbrev multipliersEncoding := framedListEncoding polyEncoding

def termWire {n d : ℕ} (t : Sparse.Term n d) : Term := (List.ofFn t.1,List.ofFn t.2)
def polyWire {n d : ℕ} (p : Sparse.Poly n d) : Poly := p.map termWire
def sourceTermWire {m n : ℕ} (t : EncodedSystem.Term m n) : SourceTerm := (t.1.val,List.ofFn t.2)
def equationWire {m n : ℕ} (e : EncodedSystem.Equation m n) : Equation := e.map sourceTermWire
def systemWire {m n : ℕ} (S : EncodedSystem.System m n) : System := S.map equationWire

structure Input where
  coefficients : ℕ
  «variables» : ℕ
  field : CommonFieldMachine.Request
  certificate : ComplexIsolation.Certificate
  equations : System
  multipliers : List Poly

abbrev Wire := ℕ × (ℕ × (CommonFieldMachine.Request ×
  (ComplexIsolation.Certificate × (System × List Poly))))
abbrev wireEncoding := pairEncoding encodingNatBool (pairEncoding encodingNatBool
  (pairEncoding CommonFieldMachine.requestEncoding
    (pairEncoding ComplexIsolation.CertificateMachine.certificateEncoding
      (pairEncoding systemEncoding multipliersEncoding))))
def Input.wire (r : Input) : Wire :=
  (r.coefficients,r.variables,r.field,r.certificate,r.equations,r.multipliers)
def Input.unwire (w : Wire) : Input := ⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2⟩
def encoding : Encoding Input Bool where
  encode r := wireEncoding.encode r.wire
  decode w := (wireEncoding.decode w).map Input.unwire
  decode_encode r := by
    change (wireEncoding.decode (wireEncoding.encode r.wire)).map Input.unwire = some r
    rw [wireEncoding.decode_encode]
    cases r
    rfl

def sourceShape (m n : ℕ) (t : SourceTerm) : Bool := decide (t.1<m ∧ t.2.length=n)
def termShape (n d : ℕ) (t : Term) : Bool := decide (t.1.length=n ∧ t.2.length=d)
def Input.shape (r : Input) : Bool := r.field.shape &&
  (decide (r.field.targets.length=r.coefficients ∧ r.multipliers.length=r.equations.length) &&
    (r.equations.all (fun e => e.all (sourceShape r.coefficients r.variables)) &&
      r.multipliers.all (fun p => p.all (termShape r.variables r.field.dimension))))

def fromCandidate {m n : ℕ} (target : Fin m → RootCode) (S : EncodedSystem.System m n)
    (r : NullstellensatzSearch.Candidate m n S.length) : Input :=
  ⟨m,n,CommonFieldMachine.fromFamily r.2.relation r.2.source r.2.expression target,
    r.2.certificate,systemWire S,List.ofFn (fun i => polyWire (r.2.multiplier i))⟩

@[simp] theorem fromCandidate_shape {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length) :
    (fromCandidate target S r).shape=true := by
  simp [fromCandidate,Input.shape,systemWire,equationWire,sourceTermWire,polyWire,termWire,
    sourceShape,termShape,List.all_eq_true,List.mem_ofFn,CommonFieldMachine.fromFamily,
    CommonFieldMachine.Request.shape]
  intro i a b x v _ ha hb
  subst a
  subst b
  simp

theorem faithful : Function.Injective encoding.encode := encoding.encode_injective
theorem fromCandidate_roundtrip {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length) :
    encoding.decode (encoding.encode (fromCandidate target S r)) = some (fromCandidate target S r) :=
  encoding.decode_encode _

theorem encoded_length (r : Input) :
    (encoding.encode r).length = 2*(encodingNatBool.encode r.coefficients).length+
      2*(encodingNatBool.encode r.variables).length+
      2*(CommonFieldMachine.requestEncoding.encode r.field).length+
      2*(ComplexIsolation.CertificateMachine.certificateEncoding.encode r.certificate).length+
      2*(systemEncoding.encode r.equations).length+(multipliersEncoding.encode r.multipliers).length+5 := by
  simp only [encoding,Input.wire,wireEncoding,pairEncoding_length]
  omega

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
