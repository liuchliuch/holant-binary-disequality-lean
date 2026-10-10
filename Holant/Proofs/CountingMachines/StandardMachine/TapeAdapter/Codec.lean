import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Paths

set_option backward.isDefEq.respectTransparency false
/-! Faithful literal Boolean storage for finite-alphabet zipper configurations.
Finite symbols have fixed-width one-hot codes. The decoder searches a fixed
finite enumeration, and the list/product framing uses terminating parsers.
No serialization running-time bound is asserted or used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter.Codec
open Computability Holant.Complexity Holant.Algebraic

variable (A : Type) [Fintype A]

def width : ℕ := Fintype.card A + 1

def symbol (a : A) : List Bool :=
  List.ofFn (fun i : Fin (width A) => decide ((Fintype.equivFin A a).val = i.val))

@[simp] theorem symbol_length (a : A) : (symbol A a).length = width A := List.length_ofFn

theorem symbol_injective : Function.Injective (symbol A) := by
  intro a b h
  have hf := List.ofFn_injective h
  let i : Fin (width A) := ⟨(Fintype.equivFin A a).val, by
    have ha := (Fintype.equivFin A a).isLt
    simp only [width]
    omega⟩
  have hb : (Fintype.equivFin A b).val = (Fintype.equivFin A a).val := by
    have hi := congrFun hf i
    simpa [i] using hi.symm
  exact (Fintype.equivFin A).injective (Fin.ext hb.symm)

/-- A finite table lookup, not an existentially selected decoder output. -/
def lookup : List A → List Bool → Option A
  | [], _ => none
  | a :: rest, bits => if symbol A a = bits then some a else lookup rest bits

theorem lookup_symbol (xs : List A) (a : A) (ha : a ∈ xs) :
    lookup A xs (symbol A a) = some a := by
  induction xs with
  | nil => simp at ha
  | cons b rest ih =>
      classical
      by_cases h : b = a
      · subst b; simp [lookup]
      · have hn : symbol A b ≠ symbol A a := fun he => h (symbol_injective A he)
        have hm : a ∈ rest := by simpa [h,Ne.symm h] using ha
        simp [lookup,hn,ih hm]

def finiteEncoding : Encoding A Bool where
  encode := symbol A
  decode := lookup A (Finset.univ.toList)
  decode_encode a := lookup_symbol A _ a (by simp)

@[simp] theorem finiteEncoding_length (a : A) :
    ((finiteEncoding A).encode a).length = width A := symbol_length A a

theorem framed_length (xs : List A) :
    ((framedListEncoding (finiteEncoding A)).encode xs).length =
      (2 * width A + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode]
  | cons a rest ih =>
      change (true :: (frame (symbol A a) ++ framedListEncode (finiteEncoding A) rest)).length = _
      simp only [List.length_cons,List.length_append,frame_length,symbol_length,List.length_cons]
      change 2 * width A + 1 + ((framedListEncoding (finiteEncoding A)).encode rest).length + 1 = _
      rw [ih]
      ring

variable {Γ Q Δ : Type} [Fintype Γ] [Fintype Q]

def tupleEncoding : Encoding (Q × (Γ × (List Γ × List Γ))) Bool :=
  framedProductEncoding (finiteEncoding Q)
    (framedProductEncoding (finiteEncoding Γ)
      (framedProductEncoding (framedListEncoding (finiteEncoding Γ))
        (framedListEncoding (finiteEncoding Γ))))

def pack (c : Config Γ Q) : Q × (Γ × (List Γ × List Γ)) :=
  (c.control,c.head,c.left,c.right)

def unpack (x : Q × (Γ × (List Γ × List Γ))) : Config Γ Q :=
  ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩

@[simp] theorem unpack_pack (c : Config Γ Q) : unpack (pack c) = c := by cases c; rfl

def configEncoding : Encoding (Config Γ Q) Bool where
  encode c := tupleEncoding.encode (pack c)
  decode bits := (tupleEncoding.decode bits).map unpack
  decode_encode c := by simp

/-- A parser inverse, proving the stored word retains control, head, both
finite list lengths, all tape symbols, and any explicit trailing blanks. -/
theorem decode_encode (c : Config Γ Q) : configEncoding.decode (configEncoding.encode c) = some c :=
  Encoding.decode_encode configEncoding c

theorem encode_injective : Function.Injective (configEncoding (Γ := Γ) (Q := Q)).encode :=
  Encoding.encode_injective configEncoding

theorem config_length (c : Config Γ Q) :
    (configEncoding.encode c).length =
      2 * width Q + 2 * width Γ + 6 +
        (4 * width Γ + 4) * c.left.length + (2 * width Γ + 2) * c.right.length := by
  simp only [configEncoding,tupleEncoding,pack,framedProductEncoding_length,
    finiteEncoding_length,framed_length]
  ring

def fixedBits : ℕ := 2 * width Q + 2 * width Γ + 6

def cellBits : ℕ := 4 * width Γ + 4

theorem config_bound (m : Model Γ Q) (c : Config Γ Q) :
    (configEncoding.encode c).length ≤ fixedBits (Γ := Γ) (Q := Q) +
      cellBits (Γ := Γ) * m.cells c := by
  rw [config_length]
  simp only [fixedBits,cellBits,Model.cells]
  nlinarith

/-- Actual encoded storage polynomial on the typed input channel. -/
def storagePolynomial (clock : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (fixedBits (Γ := Γ) (Q := Q)) +
    Polynomial.C (cellBits (Γ := Γ)) * (Polynomial.X + clock + Polynomial.C 1)

theorem prefix_bits (m : Model Γ Q) (input : Δ → Γ) (clock : Polynomial ℕ)
    (htime : m.PolyTimeOn input clock) (word : List Δ) (tokens : List (Option Bool))
    (finish : Config Γ Q)
    (ht : m.PhysicalTrace tokens (m.initialConfig (word.map input)) finish) :
    (configEncoding.encode finish).length ≤
      (storagePolynomial (Γ := Γ) (Q := Q) clock).eval word.length := by
  have htime' := htime word tokens finish ht
  have hcells := m.prefix_cells (word.map input) tokens finish (m.physicalTrace_trace tokens _ finish ht)
  simp only [List.length_map] at hcells
  have hc : m.cells finish ≤ word.length + clock.eval word.length + 1 := by omega
  have hb := config_bound m finish
  have hm := Nat.mul_le_mul_left (cellBits (Γ := Γ)) hc
  simp only [storagePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter.Codec
