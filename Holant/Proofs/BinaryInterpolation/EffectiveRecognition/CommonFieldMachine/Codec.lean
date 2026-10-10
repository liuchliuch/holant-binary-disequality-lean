import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Codec
import Holant.Proofs.AlgebraicRecognition.CommonFieldCheck


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine (polynomialEncoding rootEncoding)

abbrev coordinatesEncoding := framedListEncoding rationalEncoding
abbrev expressionsEncoding := framedListEncoding polynomialEncoding
abbrev rootsEncoding := framedListEncoding rootEncoding
abbrev ballWireEncoding := pairEncoding rationalEncoding rationalEncoding

def ballEncoding : Encoding RationalBall Bool where
  encode b := ballWireEncoding.encode (b.center, b.radius)
  decode w := (ballWireEncoding.decode w).map (fun p => ⟨p.1,p.2⟩)
  decode_encode b := by
    rw [Encoding.decode_encode]
    rfl

def boxEncoding : Encoding RationalBox Bool where
  encode b := (pairEncoding ballEncoding ballEncoding).encode (b.re,b.im)
  decode w := ((pairEncoding ballEncoding ballEncoding).decode w).map (fun p => ⟨p.1,p.2⟩)
  decode_encode b := by
    rw [Encoding.decode_encode]
    rfl

structure Request where
  dimension : ℕ
  relation : List ℚ
  box : RationalBox
  expressions : List RationalPolynomialCode
  targets : List RootCode

abbrev RequestWire := ℕ × (List ℚ × (RationalBox ×
  (List RationalPolynomialCode × List RootCode)))
abbrev requestWireEncoding := pairEncoding encodingNatBool
  (pairEncoding coordinatesEncoding (pairEncoding boxEncoding
    (pairEncoding expressionsEncoding rootsEncoding)))

def Request.wire (r : Request) : RequestWire :=
  (r.dimension,r.relation,r.box,r.expressions,r.targets)
def Request.unwire (w : RequestWire) : Request :=
  ⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2⟩

def requestEncoding : Encoding Request Bool where
  encode r := requestWireEncoding.encode r.wire
  decode w := (requestWireEncoding.decode w).map Request.unwire
  decode_encode r := by
    rw [Encoding.decode_encode]
    rfl

def Request.shape (r : Request) : Bool :=
  decide (0 < r.dimension ∧ r.relation.length = r.dimension ∧
    r.expressions.length = r.targets.length)

theorem shape_iff (r : Request) : r.shape = true ↔
    0 < r.dimension ∧ r.relation.length = r.dimension ∧
      r.expressions.length = r.targets.length := by simp [Request.shape]

/-- Reject inconsistent dimensions and unequal family lengths before evaluation. -/
def decodeRequest (w : List Bool) : Option Request := do
  let r ← requestEncoding.decode w
  if r.shape then some r else none

theorem decodeRequest_shape {w : List Bool} {r : Request}
    (h : decodeRequest w = some r) : r.shape = true := by
  unfold decodeRequest at h
  cases hd : requestEncoding.decode w with
  | none => simp [hd] at h
  | some s =>
    simp only [hd, Option.bind_some, pure, bind, Option.bind] at h
    split at h
    · cases h; assumption
    · simp at h

def fromFamily {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) : Request :=
  ⟨d+1,List.ofFn c,b,List.ofFn e,List.ofFn t⟩

@[simp] theorem fromFamily_shape {d m : ℕ} (c : PowerArithmetic.Vector d)
    (b : RationalBox) (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) :
    (fromFamily c b e t).shape = true := by simp [fromFamily, Request.shape]

@[simp] theorem decodeRequest_encode {r : Request} (h : r.shape = true) :
    decodeRequest (requestEncoding.encode r) = some r := by
  simp [decodeRequest, requestEncoding.decode_encode, h]

theorem request_faithful : Function.Injective requestEncoding.encode :=
  requestEncoding.encode_injective

/-- Exact list length, retaining empty lists, zero entries and duplicate terms. -/
def listBytes {A : Type} (e : Encoding A Bool) : List A → ℕ
  | [] => 1
  | a::as => 2*(e.encode a).length+2+listBytes e as

theorem list_length {A : Type} (e : Encoding A Bool) (xs : List A) :
    ((framedListEncoding e).encode xs).length = listBytes e xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [framedListEncoding, framedListEncode, List.length_cons,
      List.length_append, frame_length, listBytes] at *
    omega

theorem box_length (b : RationalBox) :
    (boxEncoding.encode b).length =
      4*(rationalEncoding.encode b.re.center).length +
      2*(rationalEncoding.encode b.re.radius).length +
      2*(rationalEncoding.encode b.im.center).length +
      (rationalEncoding.encode b.im.radius).length + 4 := by
  simp only [boxEncoding, ballEncoding, pairEncoding_length]
  omega

theorem request_length (r : Request) :
    (requestEncoding.encode r).length =
      2*(encodingNatBool.encode r.dimension).length +
      2*listBytes rationalEncoding r.relation + 2*(boxEncoding.encode r.box).length +
      2*listBytes polynomialEncoding r.expressions +
      listBytes rootEncoding r.targets + 4 := by
  simp only [requestEncoding, Request.wire, requestWireEncoding, pairEncoding_length,
    coordinatesEncoding, expressionsEncoding, rootsEncoding, list_length]
  omega

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
