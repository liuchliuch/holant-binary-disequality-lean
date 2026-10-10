import Holant.Proofs.Reductions.GeneralExtraction.GroupingLayout


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GroupingCompiler
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable (s b : ℕ) (arity : ℕ → ℕ) (a k : ℕ) (hk : 0 < k)

abbrev Width := k * arity a
abbrev BlockQuery := GroupingMachine.BlockQuery s b arity a k
abbrev blockEncoding := GroupingMachine.blockEncoding s b arity a k

theorem block_fits (x : BlockQuery s b arity a k) :
    (k*arity a)*x.2.val + k*arity a ≤ (RawGrouping.selected a x.1.val.vertices).length := by
  have hi := x.2.isLt
  have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hi)
  have hq := Nat.div_mul_le_self (occurrences a x.1.val) k
  dsimp only [GroupingMachine.blockCount] at hm
  have hh : k*(x.2.val+1) ≤ occurrences a x.1.val := by nlinarith
  have he := Nat.mul_le_mul_right (arity a) hh
  rw [GroupingLayout.selected_length a x.1.val x.1.property]
  nlinarith

def endpointIndex (x : BlockQuery s b arity a k) (j : Fin (k*arity a)) :
    Fin (RawGrouping.selected a x.1.val.vertices).length :=
  ⟨(k*arity a)*x.2.val+j.val, by have h := block_fits s b arity a k x; omega⟩

def endpointComputes (j : Fin (k*arity a)) : Computes (blockEncoding s b arity a k) endpointEncoding
    (fun x => (RawGrouping.selected a x.1.val.vertices).get (endpointIndex s b arity a k x j)) := by
  let ix := ((GroupingMachine.blockIndexComputes s b arity a k).andThen
    (UnaryQuotient.timesComputes (k*arity a))).andThen (UnaryQuotient.addConstantComputes j.val)
  let pre : Computes (blockEncoding s b arity a k) (ParentRowSelect.inputEncoding endpointEncoding)
      (fun x => ⟨RawGrouping.selected a x.1.val.vertices, endpointIndex s b arity a k x j⟩) :=
    recode (pairComputes ((GroupingMachine.blockSourceComputes s b arity a k).andThen
      (GroupingMachine.selectedComputes s b arity a)) ix) id (fun _ => rfl) (fun _ => rfl)
  exact pre.andThen (ParentRowSelect.computes endpointEncoding)

def blockRow (x : BlockQuery s b arity a k) : RawVertex :=
  (a, (List.finRange (k*arity a)).map fun j =>
    (RawGrouping.selected a x.1.val.vertices).get (endpointIndex s b arity a k x j))

def blockRowComputes : Computes (blockEncoding s b arity a k) vertexEncoding
    (blockRow s b arity a k) :=
  recode (pairComputes (constantComputes _ encodingNatBool a)
    (fixedListComputes (blockEncoding s b arity a k) endpointEncoding
      (fun x j => (RawGrouping.selected a x.1.val.vertices).get (endpointIndex s b arity a k x j))
      (endpointComputes s b arity a k) (List.finRange (k*arity a)))) id (fun _ => rfl) (fun _ => rfl)

theorem blockRow_ports (x : BlockQuery s b arity a k) :
    (blockRow s b arity a k x).2 =
      ((RawGrouping.selected a x.1.val.vertices).drop ((k*arity a)*x.2.val)).take (k*arity a) := by
  have hh := block_fits s b arity a k x
  apply List.ext_getElem
  · simp [blockRow, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    simp [blockRow, endpointIndex, List.get_eq_getElem, Nat.add_comm]

theorem blockRows_eq (r : Input s b arity) :
    (List.finRange (GroupingMachine.blockCount s b arity a k r)).map
      (fun i => blockRow s b arity a k ⟨r,i⟩) =
      RawGrouping.blocks a (k*arity a) (occurrences a r.val/k) (RawGrouping.selected a r.val.vertices) := by
  rw [GroupingMachine.blocks_indexed a (k*arity a)]
  apply List.ext_getElem
  · simp [GroupingMachine.blockCount]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    refine Prod.ext (by rfl) ?_
    exact blockRow_ports s b arity a k _

def blockEntriesComputes : Computes (validatedEncoding s b arity) Frame.wordEncoding
    (fun r => entries vertexEncoding
      (RawGrouping.blocks a (k*arity a) (occurrences a r.val/k) (RawGrouping.selected a r.val.vertices))) := by
  let pre : Computes (validatedEncoding s b arity)
      (ContextFlatMap.inputEncoding (validatedEncoding s b arity)
        (fun r => OccurrenceLabel.unaryPortEncoding (GroupingMachine.blockCount s b arity a k r)))
      (fun r => ⟨r,List.finRange (GroupingMachine.blockCount s b arity a k r)⟩) :=
    recode (pairComputes (identityComputes _)
      (((occurrencesComputes s b arity a).andThen (UnaryQuotient.computes k hk)).andThen
        ComponentSelection.UnaryRange.computes)) id (fun _ => rfl) (fun r => by
          change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
          rw [← finRange_values, finListEncoding]; rfl)
  let run := pre.andThen (ContextFlatMap.computes (validatedEncoding s b arity)
    (fun r => OccurrenceLabel.unaryPortEncoding (GroupingMachine.blockCount s b arity a k r)) _
    ((blockRowComputes s b arity a k).andThen (entryComputes vertexEncoding)))
  refine congrComputes run ?_
  intro r
  have h := congrArg (entries vertexEncoding) (blockRows_eq s b arity a k r)
  simp only [entries, List.flatMap_map] at h
  exact h

def rowsComputes : Computes (validatedEncoding s b arity) (framedListEncoding vertexEncoding)
    (fun r => (RawFactorGrouping.group a k r.val).vertices) := by
  let run := joinComputes (joinComputes (GroupingMachine.keptEntriesComputes s b arity a)
    (blockEntriesComputes s b arity a k hk)) (constantComputes _ Frame.wordEncoding [false])
  refine recode run id (fun _ => rfl) ?_
  intro r
  rw [GroupingLayout.group_eq_indexed_blocks a k r.val r.property]
  simpa [Frame.wordEncoding, framedListEncoding, framedListEncode, entries, List.flatMap_append, List.append_assoc] using
    entries_append_encode vertexEncoding
      (RawGrouping.keep a r.val.vertices ++ RawGrouping.blocks a (k*arity a)
        (occurrences a r.val/k) (RawGrouping.selected a r.val.vertices)) []

/-- Minimal total machine branch: k need not divide the count for execution.
Divisibility is required separately when retyping the output as a valid graph.
All arities, including arity > 1, use the same physical program construction. -/
def computes : Computes (validatedEncoding s b arity) encoding
    (fun r => RawFactorGrouping.group a k r.val) :=
  recode (pairComputes (rowsComputes s b arity a k hk) (Compiler.edgesComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

theorem primitive_bound (r : Input s b arity) :
    primitiveCost (computes s b arity a k hk).machine ((computes s b arity a k hk).outputs r).steps
      (some (Turing.initList (computes s b arity a k hk).machine.computer
        ((validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes s b arity a k hk)).eval ((validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes s b arity a k hk) r

end Holant.LocalDrafts.Hardness.GeneralExtraction.GroupingCompiler
