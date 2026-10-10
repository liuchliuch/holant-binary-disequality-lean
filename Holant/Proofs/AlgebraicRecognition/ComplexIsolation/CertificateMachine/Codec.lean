import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Soundness
import Holant.Complexity.FramedEncoding
import Holant.Complexity.FixedFieldMachines.PairEncoding


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines

abbrev Gaussian := ℚ × ℚ
abbrev gaussianEncoding := pairEncoding rationalEncoding rationalEncoding
abbrev termEncoding := pairEncoding encodingNatBool rationalEncoding
abbrev polynomialEncoding := framedListEncoding termEncoding
abbrev CertificateWire := Gaussian × (Gaussian × (ℚ × ℚ))
abbrev certificateWireEncoding := pairEncoding gaussianEncoding
  (pairEncoding gaussianEncoding (pairEncoding rationalEncoding rationalEncoding))

def certificateWire (t : Certificate) : CertificateWire :=
  (t.center, t.inverseSlope, t.radius, t.magnitude)
def certificateUnwire (w : CertificateWire) : Certificate :=
  ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩

@[simp] theorem certificateUnwire_wire (t : Certificate) :
    certificateUnwire (certificateWire t) = t := by cases t; rfl
@[simp] theorem certificateWire_unwire (w : CertificateWire) :
    certificateWire (certificateUnwire w) = w := by rcases w with ⟨a,b,c,d⟩; rfl

def certificateEncoding : Encoding Certificate Bool where
  encode t := certificateWireEncoding.encode (certificateWire t)
  decode bits := (certificateWireEncoding.decode bits).map certificateUnwire
  decode_encode t := by
    rw [Encoding.decode_encode]
    rfl

abbrev Input := RationalPolynomialCode × Certificate
abbrev inputEncoding := pairEncoding polynomialEncoding certificateEncoding
abbrev RectangleWire := (ℚ × ℚ) × (ℚ × ℚ)
abbrev rectangleWireEncoding := pairEncoding gaussianEncoding gaussianEncoding

def rectangleWire (r : RationalRectangle) : RectangleWire :=
  ((r.reLower, r.reUpper), (r.imLower, r.imUpper))
def rectangleUnwire (w : RectangleWire) : RationalRectangle :=
  ⟨w.1.1, w.1.2, w.2.1, w.2.2⟩

def rectangleEncoding : Encoding RationalRectangle Bool where
  encode r := rectangleWireEncoding.encode (rectangleWire r)
  decode bits := (rectangleWireEncoding.decode bits).map rectangleUnwire
  decode_encode r := by
    rw [Encoding.decode_encode]
    rfl

def rootEncoding : Encoding RootCode Bool where
  encode c := (pairEncoding polynomialEncoding rectangleEncoding).encode
    (c.coefficients, c.rectangle)
  decode bits := ((pairEncoding polynomialEncoding rectangleEncoding).decode bits).map
    (fun p => ⟨p.1,p.2⟩)
  decode_encode c := by
    rw [Encoding.decode_encode]
    rfl

/-- A one-bit tag followed by the literal root word. Rejection is [false]. -/
def resultEncoding : Encoding (Option RootCode) Bool where
  encode x := match x with | none => [false] | some c => true :: rootEncoding.encode c
  decode bits := match bits with
    | [false] => some none
    | true :: rest => (rootEncoding.decode rest).map some
    | _ => none
  decode_encode x := by cases x <;> simp [rootEncoding.decode_encode]

theorem input_decode_encode (x : Input) : inputEncoding.decode (inputEncoding.encode x) = some x :=
  inputEncoding.decode_encode x
theorem input_faithful : Function.Injective inputEncoding.encode := inputEncoding.encode_injective
theorem root_decode_encode (c : RootCode) : rootEncoding.decode (rootEncoding.encode c) = some c :=
  rootEncoding.decode_encode c

def polynomialBytes : RationalPolynomialCode → ℕ
  | [] => 1
  | (k,q) :: ps => 4 * (encodingNatBool.encode k).length +
      2 * (rationalEncoding.encode q).length + 4 + polynomialBytes ps

theorem polynomial_length (p : RationalPolynomialCode) :
    (polynomialEncoding.encode p).length = polynomialBytes p := by
  induction p with
  | nil => rfl
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    simp only [polynomialEncoding, framedListEncoding, framedListEncode,
      List.length_cons, List.length_append, frame_length, pairEncoding_length,
      polynomialBytes] at *
    omega

theorem certificate_length (t : Certificate) :
    (certificateEncoding.encode t).length =
      4 * (rationalEncoding.encode t.center.1).length +
      2 * (rationalEncoding.encode t.center.2).length +
      4 * (rationalEncoding.encode t.inverseSlope.1).length +
      2 * (rationalEncoding.encode t.inverseSlope.2).length +
      2 * (rationalEncoding.encode t.radius).length +
      (rationalEncoding.encode t.magnitude).length + 7 := by
  simp only [certificateEncoding, certificateWire, pairEncoding_length]
  omega

theorem input_length (x : Input) :
    (inputEncoding.encode x).length = 2 * polynomialBytes x.1 + 1 +
      (certificateEncoding.encode x.2).length := by
  rw [pairEncoding_length, polynomial_length]

end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
