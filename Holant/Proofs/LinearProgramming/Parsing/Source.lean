import Holant.Proofs.LinearProgramming.Parsing.BranchCode.Unary
import Holant.Proofs.LinearProgramming.Parsing.BranchCode.Image
import Holant.Proofs.LinearProgramming.Parsing.PartialList.Programs
import Holant.Proofs.LinearProgramming.Parsing.Scalar.Nat
import Holant.Proofs.LinearProgramming.Parsing.Scalar.Literal
import Holant.Proofs.LinearProgramming.Foundation.Parsing

/-! Strict physical parser for the original variable-size rational LP bytes.
This accepts exactly the unchanged Codec.Input encoder image and distinguishes
malformed words from solver infeasibility. No classifier or EO consumer is imported. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Source
open Holant Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Support
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure

set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
noncomputable section

/-- Reinterpret the actual strict natural-code parser using exactly the old
integer parity encoding. Its program and output bits are unchanged. -/
def integerDecode (input : List Bool) : Option ℤ :=
  (Scalar.NatCodec.encoding.decode input).map Equiv.intEquivNat.symm

def integerEncoding : Encoding ℤ Bool where
  encode := IntegerArithmetic.encoding.encode
  decode := integerDecode
  decode_encode z := by
    change (Scalar.NatCodec.encoding.decode
      (Scalar.NatCodec.encoding.encode (Equiv.intEquivNat z))).map Equiv.intEquivNat.symm = some z
    rw [Encoding.decode_encode]
    simp only [Option.map_some, Equiv.symm_apply_apply]

theorem integer_strict : PartialList.Strict integerEncoding := by
  intro input z
  constructor
  · intro h
    change (Scalar.NatCodec.encoding.decode input).map Equiv.intEquivNat.symm = some z at h
    obtain ⟨n, hn, hz⟩ := Option.map_eq_some_iff.mp h
    have he : n = Equiv.intEquivNat z := by rw [← hz]; simp only [Equiv.apply_symm_apply]
    have hw := (Scalar.NatCodec.decode_some_iff input n).mp hn
    rw [he] at hw
    exact hw
  · intro h
    rw [h]
    exact Encoding.decode_encode integerEncoding z

def integerComputes : Computes Frame.wordEncoding (optionEncoding integerEncoding) integerDecode :=
  recode Scalar.NatParser.strictComputes id (fun _ => rfl) (fun input => by
    change (optionEncoding Scalar.NatCodec.encoding).encode (Scalar.NatCodec.encoding.decode input) =
      (optionEncoding integerEncoding).encode
        ((Scalar.NatCodec.encoding.decode input).map Equiv.intEquivNat.symm)
    cases hd : Scalar.NatCodec.encoding.decode input with
    | none => rfl
    | some n =>
      simp only [optionEncoding, Option.map_some, integerEncoding,
        IntegerArithmetic.encoding, Scalar.NatCodec.encoding, encodingNatBool, Equiv.apply_symm_apply])

def rowEncoding := framedListEncoding integerEncoding
def rowsEncoding := framedListEncoding rowEncoding
def rowComputes : Computes Frame.wordEncoding (optionEncoding rowEncoding) rowEncoding.decode :=
  PartialList.Factory.computes integerEncoding integerComputes integer_strict
theorem rowStrict : PartialList.Strict rowEncoding := PartialList.list_strict _ integer_strict
def rowsComputes : Computes Frame.wordEncoding (optionEncoding rowsEncoding) rowsEncoding.decode :=
  PartialList.Factory.computes rowEncoding rowComputes rowStrict
theorem rowsStrict : PartialList.Strict rowsEncoding := PartialList.list_strict _ rowStrict

def bodyEncoding := pairEncoding rowsEncoding rowEncoding
def tailEncoding := pairEncoding BranchCode.Unary.encoding bodyEncoding
def wireEncoding := pairEncoding BranchCode.Unary.encoding tailEncoding

def bodyComputes : Computes Frame.wordEncoding (optionEncoding bodyEncoding) bodyEncoding.decode :=
  Pair.computes rowsEncoding rowEncoding rowsComputes rowComputes
def tailComputes : Computes Frame.wordEncoding (optionEncoding tailEncoding) tailEncoding.decode :=
  Pair.computes BranchCode.Unary.encoding bodyEncoding BranchCode.Unary.computes bodyComputes
def wireComputes : Computes Frame.wordEncoding (optionEncoding wireEncoding) wireEncoding.decode :=
  Pair.computes BranchCode.Unary.encoding tailEncoding BranchCode.Unary.computes tailComputes
theorem wireStrict : PartialList.Strict wireEncoding :=
  PartialList.pair_strict _ _ BranchCode.Unary.strict
    (PartialList.pair_strict _ _ BranchCode.Unary.strict
      (PartialList.pair_strict _ _ rowsStrict rowStrict))

/-- Strict decoders leave framed-list serialization unchanged. -/
private theorem list_encoder_eq {A : Type} (ea eb : Encoding A Bool)
    (he : ∀ a, ea.encode a = eb.encode a) (xs : List A) :
    (framedListEncoding ea).encode xs = (framedListEncoding eb).encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change true :: (Holant.Algebraic.frame (ea.encode a) ++ (framedListEncoding ea).encode xs) =
      true :: (Holant.Algebraic.frame (eb.encode a) ++ (framedListEncoding eb).encode xs)
    rw [he a, ih]

@[simp] theorem row_encoder (xs : List ℤ) : rowEncoding.encode xs = Codec.rowEncoding.encode xs :=
  list_encoder_eq integerEncoding IntegerArithmetic.encoding (fun _ => rfl) xs

@[simp] theorem rows_encoder (xs : List (List ℤ)) :
    rowsEncoding.encode xs = Codec.rowsEncoding.encode xs :=
  list_encoder_eq rowEncoding Codec.rowEncoding row_encoder xs

@[simp] theorem wire_encoder (p : Codec.Wire) :
    wireEncoding.encode p = Codec.wireEncoding.encode p := by
  simp only [wireEncoding, tailEncoding, bodyEncoding, Codec.wireEncoding,
    pairEncoding, BranchCode.Unary.encoding, rows_encoder, row_encoder]

/-- The encoder is literally the original LP encoder. The component parsers
add strict rejection; row order, repeated/empty rows and coefficients stay. -/
def rawEncoding : Encoding Codec.Raw Bool where
  encode := Codec.encoding.encode
  decode input := (wireEncoding.decode input).map Codec.fromWire
  decode_encode d := by
    change (wireEncoding.decode (Codec.wireEncoding.encode d.wire)).map Codec.fromWire = some d
    rw [← wire_encoder]
    rw [Encoding.decode_encode]
    rfl

@[simp] theorem raw_encoder (d : Codec.Raw) :
    rawEncoding.encode d = Codec.encoding.encode d := rfl

theorem raw_strict : PartialList.Strict rawEncoding := by
  intro input d
  constructor
  · intro h
    change (wireEncoding.decode input).map Codec.fromWire = some d at h
    obtain ⟨p, hp, hd⟩ := Option.map_eq_some_iff.mp h
    have hw := (wireStrict input p).mp hp
    rw [← hd]
    simpa only [wire_encoder, rawEncoding, Codec.encoding, Codec.fromWire, Codec.Raw.wire] using hw
  · intro h
    rw [h]
    exact Encoding.decode_encode rawEncoding d

def rawComputes : Computes Frame.wordEncoding (optionEncoding rawEncoding) rawEncoding.decode :=
  recode wireComputes id (fun _ => rfl) (fun input => by
    change (optionEncoding wireEncoding).encode (wireEncoding.decode input) =
      (optionEncoding rawEncoding).encode ((wireEncoding.decode input).map Codec.fromWire)
    cases wireEncoding.decode input with
    | none => rfl
    | some p =>
      simp only [Option.map_some, optionEncoding, rawEncoding, Codec.encoding,
        Codec.fromWire, Codec.Raw.wire, wire_encoder])

def validate (d : Codec.Raw) : Option Codec.Input :=
  if h : d.WellFormed then some ⟨d, h⟩ else none

theorem validate_some (d : Codec.Raw) (q : Codec.Input) :
    validate d = some q ↔ d = q.val := by
  constructor
  · intro h
    unfold validate at h
    split at h
    next hw => exact congrArg Subtype.val (Option.some.inj h)
    next hw => cases h
  · intro h
    subst d
    simp only [validate, q.property, dite_true]

/-- Only the existing physical row-count, RHS-count and row-width scanner is
used. Proof fields of Input do not change any encoded bit. -/
def validateComputes : Computes rawEncoding (optionEncoding Codec.inputEncoding) validate := by
  let w := ifComputes Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Parsing.validates (Scalar.Literal.someComputes Codec.encoding)
    (constantComputes Codec.encoding (optionEncoding Codec.encoding) none)
  refine recode w id (fun _ => rfl) ?_
  intro d
  change (optionEncoding Codec.encoding).encode
    (if decide d.WellFormed then some d else none) =
      (optionEncoding Codec.inputEncoding).encode (validate d)
  by_cases h : d.WellFormed <;>
    simp [validate, h, optionEncoding, Codec.inputEncoding]

def parse (input : List Bool) : Option Codec.Input := (rawEncoding.decode input).bind validate

def parseComputes : Computes Frame.wordEncoding (optionEncoding Codec.inputEncoding) parse :=
  congrComputes ((rawComputes.andThen (OptionMap.computes validateComputes)).andThen
    (OptionalValue.getDComputes (optionEncoding Codec.inputEncoding) none)) (fun input => by
      change (((rawEncoding.decode input).map validate).getD none) =
        (rawEncoding.decode input).bind validate
      cases rawEncoding.decode input <;> rfl)

/-- Exact old encoder image, including unary dimensions and physical row
shape validation. No successful-parser or rectangularity promise is input. -/
theorem parse_some_iff (input : List Bool) (d : Codec.Input) :
    parse input = some d ↔ input = Codec.inputEncoding.encode d := by
  constructor
  · intro h
    change (rawEncoding.decode input).bind validate = some d at h
    obtain ⟨r, hr, hd⟩ := Option.bind_eq_some_iff.mp h
    have he := (validate_some r d).mp hd
    have hw := (raw_strict input r).mp hr
    rw [he] at hw
    exact hw
  · intro h
    rw [h]
    have hr : rawEncoding.decode (Codec.inputEncoding.encode d) = some d.val :=
      Encoding.decode_encode rawEncoding d.val
    rw [parse, hr, Option.bind_some]
    exact (validate_some d.val d).mpr rfl

theorem parse_none_iff (input : List Bool) :
    parse input = none ↔ ¬ ∃ d : Codec.Input, input = Codec.inputEncoding.encode d := by
  constructor
  · intro h ⟨d, hd⟩
    have hs := (parse_some_iff input d).mpr hd
    rw [h] at hs
    cases hs
  · intro h
    cases hp : parse input with
    | none => rfl
    | some d => exact False.elim (h ⟨d, (parse_some_iff input d).mp hp⟩)

/-- The existing decoder plus the original encoder-image guard is a pure
specification of the installed physical parser, not a decoder instruction. -/
theorem parse_old_with_guard (input : List Bool) :
    parse input = (Codec.inputEncoding.decode input).bind
      (fun d => if Codec.inputEncoding.encode d = input then some d else none) :=
  BranchCode.Image.eq_of_image Codec.inputEncoding parse_some_iff input

/-- A legal original encoding is accepted without altering any field. -/
@[simp] theorem parse_encoded (d : Codec.Input) :
    parse (Codec.inputEncoding.encode d) = some d :=
  (parse_some_iff _ d).mpr rfl

/-- The parser is one fixed finite machine on all received words. -/
def machine : Machine := parseComputes.machine
def time : Polynomial ℕ := parseComputes.time

theorem inFP : InFP Frame.wordEncoding (optionEncoding Codec.inputEncoding) parse :=
  parseComputes.inFP

/-- Elementary push/pop/peek/load/branch/goto/halt fees of the same machine. -/
theorem primitive_bound (input : List Bool) :
    primitiveCost machine (parseComputes.outputs input).steps
      (some (initList machine.computer input)) ≤
        (primitivePolynomial parseComputes).eval input.length :=
  computes_primitive_cost parseComputes input

/-- Every reachable prefix, including malformed input and rejection cleanup. -/
theorem prefix_storage (input : List Bool) (j : ℕ)
    (hj : j ≤ (parseComputes.outputs input).steps) (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer input)) = some c) :
    stackSize c.stk ≤ input.length + (time.eval input.length) * machine.primitiveBudget := by
  have hs := machine.run_size_le (initList machine.computer input) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hj.trans (parseComputes.outputs input).steps_le_m)) _)

/-- The physical tagged response has a proved polynomial bit-length bound. -/
theorem output_length_bound (input : List Bool) :
    ((optionEncoding Codec.inputEncoding).encode (parse input)).length ≤
      parseComputes.outputBound.bound.eval input.length :=
  parseComputes.outputBound.length_le input

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Source
