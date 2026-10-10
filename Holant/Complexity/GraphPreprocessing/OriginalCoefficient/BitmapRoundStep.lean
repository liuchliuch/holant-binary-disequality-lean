import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq neighborMachine.K := neighborMachine.decidableK
local instance : DecidableEq (Stack neighborMachine) := (machine neighborMachine).decidableK

/-- One original vertex reads its old physical cursor bit. The old bitmap stays
unchanged throughout; only a false old bit invokes the actual neighbor scanner. -/
theorem vertex_run (x : Input) (i : Fin x.1.length) (cursor output : List Bool) :
    ∃ n, n≤roundPolynomial.eval (inputEncoding.encode x).length ∧
      RunsExactly (TM2.step (program neighborMachine))
        (ready neighborMachine (phase neighborMachine 4) x.1 (x.1.get i::cursor)
          (true::List.replicate i.val true) (edges x) output [])
        (ready neighborMachine (phase neighborMachine 4) x.1 cursor
          (List.replicate i.val true) (edges x) (bit x i::output) []) n := by
  cases hOld : x.1.get i with
  | true =>
    have hb : bit x i = true := by rw [bit,hOld]; rfl
    refine ⟨2,two_le_round _,?_⟩
    simpa only [hOld,hb] using true_round neighborMachine x.1 cursor (List.replicate i.val true) (edges x) output
  | false =>
    let result := NeighborScan.value (query x i)
    have hs : (fun c => c.bind neighborMachine.computer.step)^[(NeighborScan.timed (query x i)).steps]
        (some (initList neighborMachine.computer (queryWord x.1 (List.replicate i.val true) (edges x)))) =
          some (haltList neighborMachine.computer (result.isSome::resultTail result)) := by
      have original : (fun c : Option neighborMachine.Config => c.bind neighborMachine.computer.step)^[(NeighborScan.timed (query x i)).steps]
          (some (initList neighborMachine.computer (NeighborScan.inputEncoding.encode (query x i)))) =
            some (haltList neighborMachine.computer (ParentRowEncoding.parent.encode result)) :=
        (NeighborScan.timed (query x i)).evals_in_steps
      have inputEq := congrArg (fun word =>
        (fun c : Option neighborMachine.Config => c.bind neighborMachine.computer.step)^[(NeighborScan.timed (query x i)).steps]
          (some (initList neighborMachine.computer word))) (query_word x i)
      have outputEq := congrArg (fun word => some (haltList neighborMachine.computer word)) (result_word result)
      exact inputEq.symm.trans (original.trans outputEq)
    have run := false_round neighborMachine x.1 cursor (List.replicate i.val true) (edges x) output
      (resultTail result) result.isSome (NeighborScan.timed (query x i)).steps hs
    refine ⟨(NeighborScan.timed (query x i)).steps+2*(edges x).length+4*i.val+4*x.1.length+(resultTail result).length+15,?_,?_⟩
    · have hs := source_time_le x i
      have ho := source_tail_le x i
      have hb := table_length_le x
      have he := edges_length_le x
      have hi := i.isLt
      have bound : (NeighborScan.timed (query x i)).steps+2*(edges x).length+4*i.val+4*x.1.length+(resultTail result).length+15 ≤
          NeighborScan.timePolynomial.eval (2*((inputEncoding.encode x).length+1))+
            providerSize.eval (2*((inputEncoding.encode x).length+1))+10*(inputEncoding.encode x).length+15 := by
        dsimp only [result]
        omega
      simpa [roundPolynomial] using bound
    · have hb : bit x i = result.isSome := by rw [bit,hOld]; rfl
      simpa only [hOld,hb,List.length_replicate] using run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
