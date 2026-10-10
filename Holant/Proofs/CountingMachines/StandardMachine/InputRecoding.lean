import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Source
import Holant.Complexity.OutputSize

set_option backward.isDefEq.respectTransparency false
/-! Exact metadata and actual finite recoders for a change of input alphabet.
The decoding functions only certify faithful representation. All runtime
recoding is the literal scan/emission program in `Recoding.Source`. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding
open Turing Computability Holant.Complexity
variable {α β Γ Δ : Type} [Fintype Γ] [Fintype Δ]

/-- Reuse the literal word transducer on fixed faithful input/output encodings.
The equality is a specification of a fixed finite symbol map, not an assumed
machine or runtime result. The machine and time proof are constructed. -/
def wordMap (ea : Encoding α Γ) (eb : Encoding β Δ) (f : α → β)
    (code : Γ → List Δ) (encoded : ∀ a, eb.encode (f a) = (ea.encode a).flatMap code) :
    PolyTime ea eb f where
  tm := (Recoding.polyTime code).tm
  inputAlphabet := (Recoding.polyTime code).inputAlphabet
  outputAlphabet := (Recoding.polyTime code).outputAlphabet
  time := (Recoding.polyTime code).time
  outputsFun a := by
    have h := (Recoding.polyTime code).outputsFun (ea.encode a)
    simpa only [encodingList, encoded,id_eq] using h
  finiteAlphabets := (Recoding.polyTime code).finiteAlphabets

def wordBound (ea : Encoding α Γ) (eb : Encoding β Δ) (f : α → β)
    (code : Γ → List Δ) (encoded : ∀ a, eb.encode (f a) = (ea.encode a).flatMap code) :
    PolynomialOutputBound ea eb f where
  bound := Polynomial.C (Recoding.width code) * Polynomial.X
  length_le a := by
    rw [encoded]
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using
      Recoding.length_le code (ea.encode a)

def tagged (ea : Encoding α Γ) (eb : Encoding α Δ)
    (code : Γ → List Δ) (encoded : ∀ a, eb.encode a = (ea.encode a).flatMap code) :
    PolyTime (encodingProd ea (encodingList Bool)) (encodingProd eb (encodingList Bool)) id :=
  wordMap _ _ id (Recoding.taggedCode code) (fun p => by
    simpa only [id_eq,encodingProd,encodingList,encoded] using
      (Recoding.tagged_word code (ea.encode p.1) p.2).symm)

def taggedBound (ea : Encoding α Γ) (eb : Encoding α Δ)
    (code : Γ → List Δ) (encoded : ∀ a, eb.encode a = (ea.encode a).flatMap code) :
    PolynomialOutputBound (encodingProd ea (encodingList Bool))
      (encodingProd eb (encodingList Bool)) id :=
  wordBound _ _ id (Recoding.taggedCode code) (fun p => by
    simpa only [id_eq,encodingProd,encodingList,encoded] using
      (Recoding.tagged_word code (ea.encode p.1) p.2).symm)

def resultCode : Δ ⊕ Bool → List (Γ ⊕ Bool)
  | .inl _ => []
  | .inr bit => [.inr bit]

/-- A real singleton-result retagger, using the same finite recoder program. -/
def retag : PolyTime (taggedBoolEncoding Δ) (taggedBoolEncoding Γ) id :=
  wordMap _ _ id resultCode (fun _ => rfl)

def verifierBound (ea : Encoding α Γ) (accept : α × List Bool → Bool) :
    PolynomialOutputBound (encodingProd ea (encodingList Bool))
      (taggedBoolEncoding Γ) accept where
  bound := 1
  length_le _ := by simp

/-- A partial inverse is representation metadata only. The executable
one-symbol injection is the finite recoder, with no inverse callback. -/
def inverseSymbol (input : Γ → Δ) (symbol : Δ) : Option Γ := by
  classical
  exact if h : ∃ letter, input letter = symbol then some h.choose else none

theorem inverseSymbol_input (input : Γ → Δ) (hinj : Function.Injective input) (letter : Γ) :
    inverseSymbol input (input letter) = some letter := by
  classical
  rw [inverseSymbol, dif_pos ⟨letter,rfl⟩]
  congr 1
  exact hinj (Classical.choose_spec (show ∃ x, input x = input letter from ⟨letter,rfl⟩))

def inverseWord (input : Γ → Δ) : List Δ → Option (List Γ)
  | [] => some []
  | symbol :: rest => (inverseSymbol input symbol).bind fun letter =>
      (inverseWord input rest).map (letter :: ·)

theorem inverseWord_map (input : Γ → Δ) (hinj : Function.Injective input) (word : List Γ) :
    inverseWord input (word.map input) = some word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.map_cons,inverseWord,inverseSymbol_input input hinj,Option.bind_some,ih,
        Option.map_some]

def injectedEncoding (ea : Encoding α Γ) (input : Γ → Δ) (hinj : Function.Injective input) :
    Encoding α Δ where
  encode a := (ea.encode a).map input
  decode word := (inverseWord input word).bind ea.decode
  decode_encode a := by rw [inverseWord_map input hinj,Option.bind_some,Encoding.decode_encode]

@[simp] theorem injected_length (ea : Encoding α Γ) (input : Γ → Δ)
    (hinj : Function.Injective input) (a : α) :
    ((injectedEncoding ea input hinj).encode a).length = (ea.encode a).length := List.length_map input

@[simp] theorem singleton_flatMap (input : Γ → Δ) (word : List Γ) :
    word.flatMap (fun letter => [input letter]) = word.map input := by
  induction word with
  | nil => rfl
  | cons letter rest ih => simp only [List.flatMap_cons,List.map_cons,ih,List.singleton_append]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.InputRecoding
