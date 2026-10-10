import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanEdge

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

/-- Universal original-order scan: the result is the first successful original
edge/end, and every exit clears the old bitmap, target, remaining edge stream,
physical edge counter, call copies, provider scratch and finite registers. -/
theorem run_from (table : List Bool) (target : Fin table.length)
    (edges : List (Fin table.length × Fin table.length)) (index N : ℕ) (output : List Bool)
    (hB : table.length≤N) (hI : index+edges.length≤N) (hR : (edgeBits edges).length≤N) :
    ∃ n, n≤(edges.length+1)*roundBound N ∧ RunsExactly (TM2.step (program actual))
      (ready actual (.inr 4) table (List.replicate target.val true) [] []
        (edgeBits edges) (List.replicate index true) [] output)
      (haltList (machine actual).computer (ParentRowEncoding.parent.encode (searchFrom table target index edges)++output)) n := by
  induction edges generalizing index with
  | nil =>
    have run := no_neighbor actual table (List.replicate target.val true) (List.replicate index true) output
    refine ⟨table.length+target.val+index+9,?_,?_⟩
    · have ht := target.isLt
      simp only [List.length_nil,Nat.zero_add,Nat.one_mul,List.length_replicate] at *
      unfold roundBound
      omega
    · simpa only [edgeBits_nil,searchFrom,ParentRowEncoding.parent_none,List.cons_append,List.nil_append,List.length_replicate] using run
  | cons e rest ih =>
    rcases e with ⟨u,v⟩
    have hi : index≤N := by simp only [List.length_cons] at hI; omega
    have hir : index+1+rest.length≤N := by simp only [List.length_cons] at hI; omega
    have hr : (edgeBits rest).length≤N := by
      simp only [edgeBits_cons,List.length_append,ReachRound.unary_length] at hR
      omega
    obtain ⟨n,hn,step⟩ := edge_run table target u v rest index N output hB hi hr
    cases hp : predicate table target u v with
    | true =>
      refine ⟨n,?_,?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa [afterEdge,searchFrom,hp] using step
    | false =>
      cases hq : predicate table target v u with
      | true =>
        refine ⟨n,?_,?_⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa [afterEdge,searchFrom,hp,hq] using step
      | false =>
        simp [afterEdge,hp,hq] at step
        obtain ⟨later,hl,run⟩ := ih (index+1) hir hr
        refine ⟨later+n,?_,?_⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa [searchFrom,hp,hq] using step.trans run

theorem edges_le_bits {n : ℕ} (edges : List (Fin n × Fin n)) : edges.length≤(edgeBits edges).length := by
  induction edges with
  | nil => simp
  | cons e rest ih =>
    rcases e with ⟨u,v⟩
    simp only [edgeBits_cons,List.length_cons,List.length_append,ReachRound.unary_length]
    omega

def encoded (table : List Bool) (target : Fin table.length) (edges : List (Fin table.length × Fin table.length)) : List Bool :=
  Holant.Algebraic.frame table++(Holant.Algebraic.frame (List.replicate target.val true)++edgeBits edges)

noncomputable def timePolynomial : Polynomial ℕ :=
  (Polynomial.X+1)*(2*(NeighborPredicate.timePolynomial.comp (9*(Polynomial.X+1))+18*(Polynomial.X+1)+12)+30*(Polynomial.X+1))+
    Polynomial.X+2

/-- A whole clean execution from the actual serialized table/target/edge data,
with a polynomial in those actual input bits and all EOF/framing costs included. -/
theorem whole_run (table : List Bool) (target : Fin table.length) (edges : List (Fin table.length × Fin table.length)) :
    ∃ n, n≤timePolynomial.eval (encoded table target edges).length ∧
      RunsExactly (machine actual).computer.step
        (initList (machine actual).computer (encoded table target edges))
        (haltList (machine actual).computer (ParentRowEncoding.parent.encode (searchFrom table target 0 edges))) n := by
  let N := (encoded table target edges).length
  have hlen : N=2*table.length+1+(2*target.val+1+(edgeBits edges).length) := by
    simp [N,encoded,Holant.Algebraic.frame_length]
  have hB : table.length≤N := by omega
  have hR : (edgeBits edges).length≤N := by omega
  have hI : 0+edges.length≤N := by have h := edges_le_bits edges; omega
  obtain ⟨n,hn,run⟩ := run_from table target edges 0 N [] hB hI hR
  have init := (parse_table actual table (Holant.Algebraic.frame (List.replicate target.val true)++edgeBits edges)).trans
    (parse_target actual table (List.replicate target.val true) (edgeBits edges))
  have all := init.trans run
  refine ⟨n+(2*(target.val+1)+2*(table.length+1)),?_,?_⟩
  · have hE : edges.length≤N := by omega
    have hm := Nat.mul_le_mul_right (roundBound N) (Nat.add_le_add_right hE 1)
    have hp : 2*((List.replicate target.val true).length+1)+2*(table.length+1) ≤ N+2 := by
      simp only [List.length_replicate]
      omega
    have bound : n+(2*((List.replicate target.val true).length+1)+2*(table.length+1)) ≤ (N+1)*roundBound N+N+2 := by omega
    simpa [timePolynomial,roundBound,callBound,Polynomial.eval_comp,N] using bound
  · rw [initial]
    change RunsExactly (TM2.step (program actual)) _ _ _
    simpa only [encoded,ready,config,List.replicate_zero,List.append_nil,List.length_replicate] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
