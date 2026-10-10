import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelectFinish
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel
import Holant.Complexity.GraphPreprocessing.ParentRowEncoding
import Holant.Complexity.FixedFieldMachines.PairEncoding

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Computability FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def unaryDecode : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::tail => some (0,tail)
  | true::tail => (unaryDecode tail).map fun p => (p.1+1,p.2)

theorem unaryDecode_encode (n : ℕ) (suffix : List Bool) :
    unaryDecode (ReachRound.unary n++suffix)=some (n,suffix) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [unaryDecode,ReachRound.unary,List.replicate_succ] using ih

def decodeEdges : ℕ → List Bool → Option (List (ℕ × ℕ))
  | 0,bits => if bits=[] then some [] else none
  | fuel+1,bits => if bits=[] then some [] else do
    let (u,rest) ← unaryDecode bits
    let (v,tail) ← unaryDecode rest
    let edges ← decodeEdges fuel tail
    pure ((u,v)::edges)

theorem edges_le_bits (edges : List (ℕ × ℕ)) : edges.length≤(ReachRound.encode edges).length := by
  induction edges with
  | nil => simp
  | cons e edges ih =>
    rcases e with ⟨u,v⟩
    simp only [ReachRound.encode_cons,List.length_cons,List.length_append,ReachRound.unary_length]
    omega

theorem decodeEdges_encode (edges : List (ℕ × ℕ)) (fuel : ℕ) (hf : edges.length≤fuel) :
    decodeEdges fuel (ReachRound.encode edges)=some edges := by
  induction edges generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons e edges ih =>
    rcases e with ⟨u,v⟩
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr : edges.length≤fuel := by simp only [List.length_cons] at hf; omega
      have hn : ReachRound.encode ((u,v)::edges) ≠ [] := by
        intro he
        have hl := congrArg List.length he
        simp only [ReachRound.encode_cons,List.length_append,ReachRound.unary_length,List.length_nil] at hl
        omega
      rw [decodeEdges,if_neg hn,ReachRound.encode_cons]
      simp [List.append_assoc,unaryDecode_encode,ih fuel hr]

def edgeEncoding : Encoding (List (ℕ × ℕ)) Bool where
  encode := ReachRound.encode
  decode bits := decodeEdges bits.length bits
  decode_encode edges := decodeEdges_encode edges _ (edges_le_bits edges)
abbrev Input := Σ edges : List (ℕ × ℕ), Fin edges.length × Bool

def inputEncoding : Encoding Input Bool := sigmaEncoding edgeEncoding
  (fun edges => pairEncoding (OccurrenceLabel.unaryPortEncoding edges.length) ParentRowEncoding.orientation)
def value (x : Input) : ℕ := if x.2.2 then (x.1.get x.2.1).1 else (x.1.get x.2.1).2

theorem input_word (x : Input) : inputEncoding.encode x =
    Holant.Algebraic.frame (ReachRound.encode x.1)++(Holant.Algebraic.frame (List.replicate x.2.1.val true)++[x.2.2]) := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
