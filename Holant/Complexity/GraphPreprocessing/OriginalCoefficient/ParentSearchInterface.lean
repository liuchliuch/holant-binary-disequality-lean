import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchRun

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

def result (g : Graph) (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) : List Bool :=
  Holant.Algebraic.frame (List.replicate (g.depth root v.val) true)++
    ParentRowEncoding.parent.encode (some ((g.parentEnd root v).1.val,(g.parentEnd root v).2))

/-- Clean exact execution of bounded first-hit search. The budget is physically
allocated from the input bitmap; first-hit minimality identifies precisely the
existing depth and original-edge parent. -/
theorem whole_graph (g : Graph) (root : g.Vertex)
    (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    ∃ n, n≤timePolynomial.eval (word g {root} v.val.val).length ∧
      RunsExactly (machine actual).computer.step
        (initList (machine actual).computer (word g {root} v.val.val))
        (haltList (machine actual).computer (result g root v)) n := by
  let d := g.depth root v.val
  have hp : 0<d := Nat.pos_of_ne_zero (fun h => v.property ((g.depth_eq_zero root v.val).mp h))
  have hd : d≤g.vertices := g.depth_le root v.val
  have prep := prepare actual (NeighborPredicate.bitmap g {root}) (tailWord g v.val.val)
  simp only [NeighborPredicate.bitmap_length] at prep
  obtain ⟨a,ha,first⟩ := misses g root v.val (d-1) (by omega)
  obtain ⟨b,hb,last⟩ := graph_found g root v
  rw [Graph.reach_zero] at first
  have all := (prep.trans first).trans last
  refine ⟨b+(a+(5*g.vertices+2*(tailWord g v.val.val).length+8)),?_,?_⟩
  · have hv := vertices_le_width g v.val.val
    have he := tail_le_width g v.val.val
    have hw : width g v.val.val=2*g.vertices+1+(tailWord g v.val.val).length := rfl
    have hsteps : b+a≤g.vertices*roundPolynomial.eval (width g v.val.val) := by
      have ht : b+a≤d*roundPolynomial.eval (width g v.val.val) := by
        have h : d=(d-1)+1 := by omega
        calc
          b+a ≤ roundPolynomial.eval (width g v.val.val)+(d-1)*roundPolynomial.eval (width g v.val.val) := Nat.add_le_add hb ha
          _ = d*roundPolynomial.eval (width g v.val.val) := by conv_rhs => rw [h]
                                                               ring
      exact le_trans ht (Nat.mul_le_mul_right _ hd)
    have hm := Nat.mul_le_mul_right (roundPolynomial.eval (width g v.val.val)) hv
    have bound : b+(a+(5*g.vertices+2*(tailWord g v.val.val).length+8)) ≤
        width g v.val.val*roundPolynomial.eval (width g v.val.val)+4*width g v.val.val+8 := by omega
    simpa [timePolynomial,word_length] using bound
  · rw [initial]
    change RunsExactly (TM2.step (program actual)) _ _ _
    exact all

noncomputable def timed (g : Graph) (root : g.Vertex)
    (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    TM2OutputsInTime (machine actual).computer (word g {root} v.val.val) (some (result g root v))
      (timePolynomial.eval (word g {root} v.val.val).length) where
  steps := Classical.choose (whole_graph g root v)
  evals_in_steps := (Classical.choose_spec (whole_graph g root v)).2
  steps_le_m := (Classical.choose_spec (whole_graph g root v)).1

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C (machine actual).primitiveBudget
theorem primitive_bound (g : Graph) (root : g.Vertex)
    (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    primitiveCost (machine actual) (timed g root v).steps
      (some (initList (machine actual).computer (word g {root} v.val.val))) ≤
        primitivePolynomial.eval (word g {root} v.val.val).length := by
  have h := Nat.mul_le_mul_right (machine actual).primitiveBudget (timed g root v).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
