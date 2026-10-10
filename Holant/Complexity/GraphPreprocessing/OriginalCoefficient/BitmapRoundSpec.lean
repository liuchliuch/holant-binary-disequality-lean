import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundControl
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundPrepare

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev neighborMachine : Machine := NeighborScan.machine NeighborScan.actual
abbrev Input := Σ table : List Bool, List (Fin table.length × Fin table.length)
def inputEncoding : Encoding Input Bool := sigmaEncoding Frame.wordEncoding (fun table => NeighborScan.edgeEncoding table.length)
def edges (x : Input) : List Bool := NeighborScan.edgeBits x.2
def query (x : Input) (i : Fin x.1.length) : NeighborScan.Input := ⟨x.1,i,x.2⟩
def bit (x : Input) (i : Fin x.1.length) : Bool := x.1.get i || (NeighborScan.value (query x i)).isSome
def value (x : Input) : List Bool := List.ofFn (bit x)

@[simp] theorem input_word (x : Input) : inputEncoding.encode x = Holant.Algebraic.frame x.1++edges x := rfl
@[simp] theorem value_length (x : Input) : (value x).length=x.1.length := by simp [value]
@[simp] theorem query_word (x : Input) (i : Fin x.1.length) :
    NeighborScan.inputEncoding.encode (query x i) = queryWord x.1 (List.replicate i.val true) (edges x) := rfl

def resultTail : Option (ℕ × Bool) → List Bool
  | none => []
  | some (index,side) => Holant.Algebraic.frame (List.replicate index true)++[side]

theorem result_word (p : Option (ℕ × Bool)) : ParentRowEncoding.parent.encode p = p.isSome::resultTail p := by
  cases p with
  | none => rfl
  | some p => cases p; rfl

theorem table_length_le (x : Input) : x.1.length≤(inputEncoding.encode x).length := by
  simp only [input_word,List.length_append,Holant.Algebraic.frame_length]
  omega
theorem edges_length_le (x : Input) : (edges x).length≤(inputEncoding.encode x).length := by
  simp only [input_word,List.length_append,Holant.Algebraic.frame_length]
  omega

theorem query_length (x : Input) (i : Fin x.1.length) :
    (NeighborScan.inputEncoding.encode (query x i)).length≤2*((inputEncoding.encode x).length+1) := by
  have hi := i.isLt
  simp only [query_word,input_word,queryWord,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

/-- The provider output-size polynomial follows from the actual finite machine's
primitive pushes and clean timing theorem, rather than a supplied annotation. -/
noncomputable def providerSize : Polynomial ℕ := NeighborScan.computes.outputBound.bound
noncomputable def roundPolynomial : Polynomial ℕ :=
  NeighborScan.timePolynomial.comp (2*(Polynomial.X+1))+providerSize.comp (2*(Polynomial.X+1))+10*Polynomial.X+15

theorem source_time_le (x : Input) (i : Fin x.1.length) :
    (NeighborScan.timed (query x i)).steps≤NeighborScan.timePolynomial.eval (2*((inputEncoding.encode x).length+1)) :=
  le_trans (NeighborScan.timed (query x i)).steps_le_m
    (natPolynomial_eval_mono NeighborScan.timePolynomial (query_length x i))

theorem source_tail_le (x : Input) (i : Fin x.1.length) :
    (resultTail (NeighborScan.value (query x i))).length≤providerSize.eval (2*((inputEncoding.encode x).length+1)) := by
  have h := NeighborScan.computes.outputBound.length_le (query x i)
  have hp := natPolynomial_eval_mono providerSize (query_length x i)
  rw [result_word,List.length_cons] at h
  exact le_trans (Nat.le_of_succ_le h) hp

theorem two_le_round (N : ℕ) : 2≤roundPolynomial.eval N := by
  simp [roundPolynomial]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
