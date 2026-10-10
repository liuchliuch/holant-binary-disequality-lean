import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

theorem row_step (edges : List (ℕ × ℕ)) (target : ℕ) (row : Graph.ParentRow) (valid : ParentOpposite.Valid (edges,row))
    (N i : ℕ) (he : (ReachRound.encode edges).length≤N) (ht : target≤N)
    (hr : (ParentRowEncoding.row.encode row).length≤N) (hi : i≤N) (input rev : List Bool) :
    ∃ n, n≤roundPolynomial.eval N ∧ RunsExactly (TM2.step (program actual))
      (ready actual (.inr 4) (true::(Holant.Algebraic.frame (ParentRowEncoding.row.encode row)++input))
        (ReachRound.encode edges) (List.replicate target true) (List.replicate i true) rev [])
      (ready actual (.inr 4) input (ReachRound.encode edges) (List.replicate target true) (List.replicate (i+1) true)
        (if predicate edges target row then (childEntry i).reverse++rev else rev) []) n := by
  let q : ChildPredicate.Input := (target,⟨(edges,row),valid⟩)
  let witness := ChildPredicate.timed q
  let n := witness.steps
  have hp : ChildPredicate.value q=predicate edges target row := by
    simp only [predicate,dif_pos valid]
    rfl
  have source : (fun c => c.bind actual.computer.step)^[n]
      (some (initList actual.computer (queryWord (ReachRound.encode edges) (List.replicate target true) (ParentRowEncoding.row.encode row)))) =
      some (haltList actual.computer [ChildPredicate.value q]) := witness.evals_in_steps
  have hs := source.trans (congrArg (fun bit => some (haltList actual.computer [bit])) hp)
  have hn : n≤ChildPredicate.timePolynomial.eval (6*(N+1)) :=
    le_trans witness.steps_le_m (natPolynomial_eval_mono ChildPredicate.timePolynomial (query_length edges target row valid N he ht hr))
  cases hb : predicate edges target row with
  | false =>
    rw [hb] at hs
    have run := miss_exact actual input (ReachRound.encode edges) (List.replicate target true) (List.replicate i true) rev []
      (ParentRowEncoding.row.encode row) n hs
    refine ⟨n+4*(ParentRowEncoding.row.encode row).length+4*(ReachRound.encode edges).length+4*target+17,?_,?_⟩
    · simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
      omega
    · simpa only [List.length_replicate,List.replicate_succ,Bool.false_eq_true,↓reduceIte] using run
  | true =>
    rw [hb] at hs
    have run := match_exact actual input (ReachRound.encode edges) (List.replicate target true) rev []
      (ParentRowEncoding.row.encode row) i n hs
    refine ⟨n+4*(ParentRowEncoding.row.encode row).length+4*(ReachRound.encode edges).length+4*target+3*i+21,?_,?_⟩
    · simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
      omega
    · simpa only [List.length_replicate,↓reduceIte] using run

/-- Every original row is consumed once. The counter is its original index;
matched IDs accumulate only as reversed output bits, preserving list order. -/
theorem loop (edges : List (ℕ × ℕ)) (target : ℕ) (rows : List Graph.ParentRow)
    (valid : ∀ row∈rows, ParentOpposite.Valid (edges,row))
    (N : ℕ) (he : (ReachRound.encode edges).length≤N) (ht : target≤N)
    (hr : ∀ row∈rows, (ParentRowEncoding.row.encode row).length≤N)
    (i : ℕ) (hi : i+rows.length≤N) (rev : List Bool) :
    ∃ n, n≤rows.length*roundPolynomial.eval N+1 ∧ RunsExactly (TM2.step (program actual))
      (ready actual (.inr 4) (framedListEncode ParentRowEncoding.row rows) (ReachRound.encode edges)
        (List.replicate target true) (List.replicate i true) rev [])
      (ready actual (.inr 30) [] (ReachRound.encode edges) (List.replicate target true)
        (List.replicate (i+rows.length) true) ((bits (childrenFrom edges target i rows)).reverse++rev) []) n := by
  induction rows generalizing i rev with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa only [framedListEncode,List.length_nil,Nat.add_zero,childrenFrom,bits_nil,List.reverse_nil,List.nil_append,Bool.false_eq_true,↓reduceIte] using
      runsExactly_one (loop_marker actual [] (ReachRound.encode edges) (List.replicate target true) (List.replicate i true) rev [] false)
  | cons row rows ih =>
    have hv := valid row (by simp)
    have hrow := hr row (by simp)
    have hr' : ∀ r∈rows, (ParentRowEncoding.row.encode r).length≤N := fun r h => hr r (by simp [h])
    have hv' : ∀ r∈rows, ParentOpposite.Valid (edges,r) := fun r h => valid r (by simp [h])
    obtain ⟨a,ha,first⟩ := row_step edges target row hv N i he ht hrow (by simp only [List.length_cons] at hi; omega)
      (framedListEncode ParentRowEncoding.row rows) rev
    obtain ⟨b,hb,last⟩ := ih hv' hr' (i+1) (by simp only [List.length_cons] at hi; omega)
      (if predicate edges target row then (childEntry i).reverse++rev else rev)
    refine ⟨b+a,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have all := first.trans last
      have hc : i+(row::rows).length=i+1+rows.length := by simp; omega
      cases hp : predicate edges target row <;>
        simpa only [framedListEncode,childrenFrom,hp,Bool.false_eq_true,↓reduceIte,
          bits_cons,List.reverse_append,List.append_assoc,hc] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
