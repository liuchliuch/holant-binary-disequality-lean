import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchFinish
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
import Holant.OneHot.Computable.Rooted

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev actual : Machine := ParentProbe.machine

def tailWord (g : Graph) (target : g.Vertex) : List Bool :=
  Holant.Algebraic.frame (List.replicate target.val true)++ReachRound.encode (ReachRound.graphEdges g)
def word (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) : List Bool :=
  Holant.Algebraic.frame (NeighborPredicate.bitmap g s)++tailWord g target
def width (g : Graph) (target : g.Vertex) : ℕ := 2*g.vertices+1+(tailWord g target).length

@[simp] theorem word_length (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    (word g s target).length=width g target := by simp [word,width,Holant.Algebraic.frame_length]
theorem vertices_le_width (g : Graph) (target : g.Vertex) : g.vertices≤width g target := by unfold width; omega
theorem tail_le_width (g : Graph) (target : g.Vertex) : (tailWord g target).length≤width g target := by unfold width; omega

noncomputable def roundPolynomial : Polynomial ℕ := ParentProbe.timePolynomial+20*Polynomial.X+22
noncomputable def timePolynomial : Polynomial ℕ := Polynomial.X*roundPolynomial+4*Polynomial.X+8

theorem neighbor_none (g : Graph) (root : g.Vertex) (v : g.Fiber root) (k : ℕ)
    (hk : k+1<g.depth root v) : (g.neighborRun (g.reach root k) v.val).1=none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro q hq
  change (g.neighborRun (g.reach root k) v.val).1=some q at hq
  have hp : (g.neighborRun (g.reach root k) v.val).1.isSome := by simpa [hq]
  have hn := (g.neighborRun_spec _ _).mp hp
  have hm : v.val∈g.reach root (k+1) := by rw [Graph.reach_succ,Graph.mem_round]; exact Or.inr hn
  exact g.not_mem_before_depth root v hk hm

theorem parent_some (g : Graph) (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    (g.neighborRun (g.reach root (g.depth root v.val-1)) v.val.val).1 = some (g.parentEnd root v) := by
  unfold Graph.parentEnd
  exact (Option.some_get _).symm

noncomputable def provider (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    TM2OutputsInTime actual.computer (word g s target)
      (some (Holant.Algebraic.frame (NeighborPredicate.bitmap g (g.round s))++
        ParentRowEncoding.parent.encode ((g.neighborRun s target).1.map (fun q => (q.1.val,q.2)))))
      (ParentProbe.timePolynomial.eval (width g target)) := by
  have he : NeighborScan.inputWord (NeighborPredicate.bitmap g s) (List.replicate target.val true)
      (ReachRound.graphEdges g) = word g s target := by
    simp [NeighborScan.inputWord,word,tailWord,List.append_assoc]
  simpa only [he,word_length] using ParentProbe.graph_timed g s target

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
