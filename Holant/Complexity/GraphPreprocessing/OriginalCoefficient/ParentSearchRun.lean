import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

theorem graph_miss (g : Graph) (root : g.Vertex) (v : g.Fiber root) (k : ℕ)
    (hk : k+1<g.depth root v) (index depth : List Bool) :
    ∃ n, n≤roundPolynomial.eval (width g v.val) ∧ RunsExactly (TM2.step (program actual))
      (ready actual (phase actual 5) (NeighborPredicate.bitmap g (g.reach root k)) [] (true::index) (tailWord g v.val) depth [])
      (ready actual (phase actual 5) (NeighborPredicate.bitmap g (g.reach root (k+1))) [] index (tailWord g v.val) (true::depth) []) n := by
  let witness := provider g (g.reach root k) v.val
  let n := witness.steps
  have hs : (fun c => c.bind actual.computer.step)^[n]
      (some (initList actual.computer (word g (g.reach root k) v.val))) =
        some (haltList actual.computer (Holant.Algebraic.frame (NeighborPredicate.bitmap g (g.round (g.reach root k)))++
          ParentRowEncoding.parent.encode ((g.neighborRun (g.reach root k) v.val).1.map (fun q => (q.1.val,q.2))))) :=
    witness.evals_in_steps
  rw [neighbor_none g root v k hk] at hs
  have run := miss_exact actual (NeighborPredicate.bitmap g (g.reach root k))
    (NeighborPredicate.bitmap g (g.round (g.reach root k))) index (tailWord g v.val) depth n hs
  have ht : n≤ParentProbe.timePolynomial.eval (width g v.val) := witness.steps_le_m
  refine ⟨n+2*(tailWord g v.val).length+9*g.vertices+14,?_,?_⟩
  · have hv := vertices_le_width g v.val
    have he := tail_le_width g v.val
    have hb : n+2*(tailWord g v.val).length+9*g.vertices+14 ≤
        ParentProbe.timePolynomial.eval (width g v.val)+20*width g v.val+22 := by omega
    simpa [roundPolynomial] using hb
  · simp only [NeighborPredicate.bitmap_length,←Graph.reach_succ] at run
    convert run using 1 <;> omega

theorem misses (g : Graph) (root : g.Vertex) (v : g.Fiber root) (k : ℕ) (hk : k<g.depth root v) :
    ∃ n, n≤k*roundPolynomial.eval (width g v.val) ∧ RunsExactly (TM2.step (program actual))
      (ready actual (phase actual 5) (NeighborPredicate.bitmap g (g.reach root 0)) [] (List.replicate g.vertices true) (tailWord g v.val) [] [])
      (ready actual (phase actual 5) (NeighborPredicate.bitmap g (g.reach root k)) [] (List.replicate (g.vertices-k) true)
        (tailWord g v.val) (List.replicate k true) []) n := by
  induction k with
  | zero => exact ⟨0,by simp,by simp only [Nat.sub_zero,List.replicate_zero]; rfl⟩
  | succ k ih =>
    obtain ⟨a,ha,first⟩ := ih (by omega)
    have hd := g.depth_le root v
    have hc : g.vertices-k=(g.vertices-(k+1))+1 := by omega
    obtain ⟨b,hb,rest⟩ := graph_miss g root v k hk (List.replicate (g.vertices-(k+1)) true) (List.replicate k true)
    rw [hc,List.replicate_succ] at first
    refine ⟨b+a,?_,?_⟩
    · nlinarith
    · simpa only [List.replicate_succ] using first.trans rest

theorem graph_found (g : Graph) (root : g.Vertex)
    (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    ∃ n, n≤roundPolynomial.eval (width g v.val.val) ∧ RunsExactly (TM2.step (program actual))
      (ready actual (phase actual 5) (NeighborPredicate.bitmap g (g.reach root (g.depth root v.val-1))) []
        (List.replicate (g.vertices-(g.depth root v.val-1)) true) (tailWord g v.val.val)
        (List.replicate (g.depth root v.val-1) true) [])
      (haltList (machine actual).computer (Holant.Algebraic.frame (List.replicate (g.depth root v.val) true)++
        ParentRowEncoding.parent.encode (some ((g.parentEnd root v).1.val,(g.parentEnd root v).2)))) n := by
  let d := g.depth root v.val
  have hd : d≤g.vertices := g.depth_le root v.val
  have hp : 0<d := Nat.pos_of_ne_zero (fun h => v.property ((g.depth_eq_zero root v.val).mp h))
  let witness := provider g (g.reach root (d-1)) v.val.val
  let n := witness.steps
  have hs : (fun c => c.bind actual.computer.step)^[n]
      (some (initList actual.computer (word g (g.reach root (d-1)) v.val.val))) =
        some (haltList actual.computer (Holant.Algebraic.frame (NeighborPredicate.bitmap g (g.round (g.reach root (d-1))))++
          ParentRowEncoding.parent.encode ((g.neighborRun (g.reach root (d-1)) v.val.val).1.map (fun q => (q.1.val,q.2))))) :=
    witness.evals_in_steps
  rw [parent_some g root v] at hs
  have run := found_exact actual (NeighborPredicate.bitmap g (g.reach root (d-1)))
    (NeighborPredicate.bitmap g (g.round (g.reach root (d-1)))) (List.replicate (g.vertices-d) true)
    (tailWord g v.val.val) (List.replicate (d-1) true)
    (Holant.Algebraic.frame (List.replicate (g.parentEnd root v).1.val true)++[(g.parentEnd root v).2]) n hs
  have hn : n≤ParentProbe.timePolynomial.eval (width g v.val.val) := witness.steps_le_m
  refine ⟨n+3*(tailWord g v.val.val).length+8*g.vertices+(g.vertices-d)+2*(d-1)+22,?_,?_⟩
  · have hv := vertices_le_width g v.val.val
    have he := tail_le_width g v.val.val
    have hb : n+3*(tailWord g v.val.val).length+8*g.vertices+(g.vertices-d)+2*(d-1)+22 ≤
        ParentProbe.timePolynomial.eval (width g v.val.val)+20*width g v.val.val+22 := by omega
    simpa [roundPolynomial] using hb
  · have hi : g.vertices-(d-1)=(g.vertices-d)+1 := by omega
    have hdepth : List.replicate d true = true::List.replicate (d-1) true := by
      have h : d=(d-1)+1 := by omega
      conv_lhs => rw [h,List.replicate_succ]
    simp only [NeighborPredicate.bitmap_length,List.length_replicate] at run
    dsimp only [d] at hi hdepth run ⊢
    simp only [hi,List.replicate_succ,hdepth,ParentRowEncoding.parent_some]
    convert run using 1 <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
