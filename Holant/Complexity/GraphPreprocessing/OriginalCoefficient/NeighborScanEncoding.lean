import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanRun

/-! Faithful codecs for the actual scan entry bytes. The edge decoder consumes
the same two false-terminated unary fields as the finite machine; it rejects
missing delimiters and original vertex IDs outside the supplied bitmap. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def unaryDecode : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::tail => some (0,tail)
  | true::tail => (unaryDecode tail).map fun p => (p.1+1,p.2)

theorem unaryDecode_encode (n : ℕ) (suffix : List Bool) :
    unaryDecode (ReachRound.unary n++suffix) = some (n,suffix) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ReachRound.unary,List.replicate_succ,unaryDecode] using ih

def edgeDecode (n : ℕ) : ℕ → List Bool → Option (List (Fin n × Fin n))
  | 0, bits => if bits=[] then some [] else none
  | fuel+1, bits => if bits=[] then some [] else do
      let (u,rest) ← unaryDecode bits
      let (v,tail) ← unaryDecode rest
      if hu : u<n then
        if hv : v<n then
          let edges ← edgeDecode n fuel tail
          pure ((⟨u,hu⟩,⟨v,hv⟩)::edges)
        else none
      else none

theorem edgeDecode_encode {n : ℕ} (edges : List (Fin n × Fin n)) (fuel : ℕ) (hf : edges.length≤fuel) :
    edgeDecode n fuel (edgeBits edges) = some edges := by
  induction edges generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons e rest ih =>
    rcases e with ⟨u,v⟩
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      have hr : rest.length≤fuel := by simp only [List.length_cons] at hf; omega
      have hne : edgeBits ((u,v)::rest) ≠ [] := by
        intro h
        have hl := congrArg List.length h
        simp only [edgeBits_cons,List.length_append,ReachRound.unary_length,List.length_nil] at hl
        omega
      rw [edgeDecode,if_neg hne,edgeBits_cons]
      simp only [List.append_assoc,unaryDecode_encode,Option.bind_some]
      simp [unaryDecode_encode,u.isLt,v.isLt,ih fuel hr]

def edgeEncoding (n : ℕ) : Encoding (List (Fin n × Fin n)) Bool where
  encode := edgeBits
  decode bits := edgeDecode n bits.length bits
  decode_encode edges := edgeDecode_encode edges _ (edges_le_bits edges)

abbrev Input := Σ table : List Bool, Fin table.length × List (Fin table.length × Fin table.length)

def inputEncoding : Encoding Input Bool := sigmaEncoding Frame.wordEncoding
  (fun table => pairEncoding (OccurrenceLabel.unaryPortEncoding table.length) (edgeEncoding table.length))

def value (x : Input) : Option (ℕ × Bool) := searchFrom x.1 x.2.1 0 x.2.2

@[simp] theorem input_word (x : Input) : inputEncoding.encode x = encoded x.1 x.2.1 x.2.2 := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
