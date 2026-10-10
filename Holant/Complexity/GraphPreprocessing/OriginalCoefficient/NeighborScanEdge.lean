import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

def afterEdge (table : List Bool) (target u v : Fin table.length)
    (rest : List (Fin table.length × Fin table.length)) (index : ℕ) (output : List Bool) : (machine actual).Config :=
  if predicate table target u v then haltList (machine actual).computer (ParentRowEncoding.parent.encode (some (index,false))++output)
  else if predicate table target v u then haltList (machine actual).computer (ParentRowEncoding.parent.encode (some (index,true))++output)
  else ready actual (.inr 4) table (List.replicate target.val true) [] [] (edgeBits rest) (List.replicate (index+1) true) [] output

/-- One original edge is tested in its literal false-end/true-end order, with
the first successful orientation emitted before any later edge is inspected. -/
theorem edge_run (table : List Bool) (target u v : Fin table.length)
    (rest : List (Fin table.length × Fin table.length)) (index N : ℕ) (output : List Bool)
    (hB : table.length≤N) (hI : index≤N) (hR : (edgeBits rest).length≤N) :
    ∃ n, n≤roundBound N ∧ RunsExactly (TM2.step (program actual))
      (ready actual (.inr 4) table (List.replicate target.val true) [] []
        (edgeBits ((u,v)::rest)) (List.replicate index true) [] output)
      (afterEdge table target u v rest index output) n := by
  have ht := target.isLt
  have hu := u.isLt
  have hv := v.isLt
  have hcf := callTime_le table target u v N hB
  have hct := callTime_le table target v u N hB
  have parse := parse_edge actual table (List.replicate target.val true) (edgeBits rest) (List.replicate index true) output u.val v.val
  rw [← edgeBits_cons] at parse
  have invoke := call_test table target u v (edgeBits rest) (List.replicate index true) [] output
  have answer := result_step actual table (List.replicate target.val true) (List.replicate u.val true)
    (List.replicate v.val true) (edgeBits rest) (List.replicate index true) [] output (predicate table target u v)
  have first := (parse.trans invoke).trans (runsExactly_one answer)
  cases hp : predicate table target u v with
  | true =>
    simp only [hp,ite_true] at first
    have finish := found actual table (List.replicate target.val true) (List.replicate u.val true)
      (List.replicate v.val true) (edgeBits rest) (List.replicate index true) output false
    have all := first.trans finish
    refine ⟨(2*index+(edgeBits rest).length+table.length+target.val+u.val+v.val+12)+
      (1+(callTime table target u v+(u.val+v.val+3))),?_,?_⟩
    · unfold roundBound; omega
    · simpa [afterEdge,hp,ParentRowEncoding.parent_some,List.append_assoc] using all
  | false =>
    simp only [hp,ite_false] at first
    have fail := runsExactly_one (first_failed actual table (List.replicate target.val true) (List.replicate u.val true)
      (List.replicate v.val true) (edgeBits rest) (List.replicate index true) output)
    have swap := swap_ends actual table (List.replicate target.val true) (List.replicate u.val true)
      (List.replicate v.val true) (edgeBits rest) (List.replicate index true) output
    have invoke' := call_test table target v u (edgeBits rest) (List.replicate index true) [true] output
    have answer' := result_step actual table (List.replicate target.val true) (List.replicate v.val true)
      (List.replicate u.val true) (edgeBits rest) (List.replicate index true) [true] output (predicate table target v u)
    have second := (((first.trans fail).trans swap).trans invoke').trans (runsExactly_one answer')
    cases hq : predicate table target v u with
    | true =>
      simp only [hq,ite_true] at second
      have finish := found actual table (List.replicate target.val true) (List.replicate v.val true)
        (List.replicate u.val true) (edgeBits rest) (List.replicate index true) output true
      have all := second.trans finish
      refine ⟨(2*index+(edgeBits rest).length+table.length+target.val+v.val+u.val+12)+
        (1+(callTime table target v u+((4*u.val+2*v.val+7)+
          (1+(1+(callTime table target u v+(u.val+v.val+3))))))),?_,?_⟩
      · unfold roundBound; omega
      · simpa [afterEdge,hp,hq,ParentRowEncoding.parent_some,List.append_assoc] using all
    | false =>
      simp only [hq,ite_false] at second
      have fail' := runsExactly_one (second_failed actual table (List.replicate target.val true) (List.replicate v.val true)
        (List.replicate u.val true) (edgeBits rest) (List.replicate index true) output)
      have advance := advance_edge actual table (List.replicate target.val true) (List.replicate v.val true)
        (List.replicate u.val true) (edgeBits rest) (List.replicate index true) output
      have all := (second.trans fail').trans advance
      refine ⟨(v.val+u.val+3)+(1+(1+(callTime table target v u+((4*u.val+2*v.val+7)+
        (1+(1+(callTime table target u v+(u.val+v.val+3)))))))),?_,?_⟩
      · unfold roundBound; omega
      · simpa [afterEdge,hp,hq,List.replicate_succ] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
