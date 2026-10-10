import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Preparation
import Holant.Complexity.UniversalPairReduction.Arithmetic

/-! Fixed-field Boolean-stack postprocessors apply the native-X circle factor
and keep the zero-occurrence branch exact. All arithmetic has real bit cost. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n)

abbrev symmetricAnswerEncoding := pairEncoding F.encoding flagsEncoding
abbrev collectedEncoding := pairEncoding F.encoding
  (pairEncoding F.encoding (pairEncoding F.encoding flagsEncoding))

def corrected (x : K × Flags) : K := if x.2.1 then 2*x.1 else x.1

def correctedComputes : Computes (symmetricAnswerEncoding F) F.encoding corrected := by
  let answer := Wiring.firstComputes F.encoding flagsEncoding
  let test := (Wiring.secondComputes F.encoding flagsEncoding).andThen
    (Wiring.firstComputes encodingBoolBool encodingBoolBool)
  exact ifComputes test
    (congrComputes (scaleComputes F answer 2) (fun x => mul_comm x.1 2)) answer

def symmetricPost (x : K × Flags) : K := if x.2.2 then corrected x/2 else x.1

def symmetricPostComputes : Computes (symmetricAnswerEncoding F) F.encoding symmetricPost := by
  let answer := Wiring.firstComputes F.encoding flagsEncoding
  let test := (Wiring.secondComputes F.encoding flagsEncoding).andThen
    (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  exact ifComputes test ((correctedComputes F).andThen (halfComputes F)) answer

abbrev Collected := K × (K × (K × Flags))

def asymmetricPost (b c : K) (x : Collected (K:=K)) : K :=
  if x.2.2.2.2 then (corrected (x.1,x.2.2.2)+(x.2.1-x.2.2.1)/(b-c))/2 else x.1

def collectedFlagsComputes : Computes (collectedEncoding F) flagsEncoding (fun x => x.2.2.2) :=
  ((Wiring.secondComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding flagsEncoding))).andThen
    (Wiring.secondComputes F.encoding (pairEncoding F.encoding flagsEncoding))).andThen
      (Wiring.secondComputes F.encoding flagsEncoding)

def asymmetricPostComputes (b c : K) :
    Computes (collectedEncoding F) F.encoding (asymmetricPost b c) := by
  let first := Wiring.firstComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding flagsEncoding))
  let tail := Wiring.secondComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding flagsEncoding))
  let plus := tail.andThen (Wiring.firstComputes F.encoding (pairEncoding F.encoding flagsEncoding))
  let minus := (tail.andThen (Wiring.secondComputes F.encoding (pairEncoding F.encoding flagsEncoding))).andThen
    (Wiring.firstComputes F.encoding flagsEncoding)
  let flags := collectedFlagsComputes F
  let test := flags.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  let adjusted := (pairComputes first flags).andThen (correctedComputes F)
  let answers := pairComputes adjusted (pairComputes plus minus)
  exact ifComputes test (answers.andThen (asymmetricComputes F b c)) first

end
end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
