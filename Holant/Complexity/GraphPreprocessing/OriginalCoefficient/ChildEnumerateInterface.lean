import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateRun

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

/-- Clean original-order child filtering. Every bound used by the loop is
proved here from the actual entry bytes; no size or counter certificate enters. -/
theorem whole_run (x : Input) :
    ∃ n, n≤timePolynomial.eval (inputEncoding.encode x).length ∧
      RunsExactly (machine actual).computer.step (initList (machine actual).computer (inputEncoding.encode x))
        (haltList (machine actual).computer (outputEncoding.encode (value x))) n := by
  let N := (inputEncoding.encode x).length
  obtain ⟨he,ht,hv,hr⟩ := input_bounds x
  change (ReachRound.encode x.val.1).length≤N at he
  change x.val.2.1≤N at ht
  change x.val.2.2.length≤N at hv
  change ∀ row∈x.val.2.2, (ParentRowEncoding.row.encode row).length≤N at hr
  have prep := prepare actual (ReachRound.encode x.val.1) (List.replicate x.val.2.1 true)
    (framedListEncode ParentRowEncoding.row x.val.2.2)
  obtain ⟨n,hn,run⟩ := loop x.val.1 x.val.2.1 x.val.2.2 x.property N he ht hr 0 (by simpa using hv) []
  simp only [List.replicate_zero,Nat.zero_add,List.append_nil] at run
  have last := finish actual (ReachRound.encode x.val.1) (List.replicate x.val.2.1 true)
    (List.replicate x.val.2.2.length true) (bits (value x)).reverse
  simp only [List.reverse_reverse,bits_encode,List.length_replicate,List.length_reverse] at last
  have all := (prep.trans run).trans last
  refine ⟨((ReachRound.encode x.val.1).length+x.val.2.1+x.val.2.2.length+(bits (value x)).length+7)+
    (n+(2*(ReachRound.encode x.val.1).length+2*(List.replicate x.val.2.1 true).length+4)),?_,?_⟩
  · have hb := children_bits_length x.val.1 x.val.2.1 0 x.val.2.2
    change (bits (value x)).length≤x.val.2.2.length*(2*(0+x.val.2.2.length)+2) at hb
    have hm := Nat.mul_le_mul hv (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) 2)
    have hout : (bits (value x)).length≤2*(N+1)^2 := by nlinarith
    have hnr := Nat.mul_le_mul_right (roundPolynomial.eval N) hv
    have bound : ((ReachRound.encode x.val.1).length+x.val.2.1+x.val.2.2.length+(bits (value x)).length+7)+
        (n+(2*(ReachRound.encode x.val.1).length+2*(List.replicate x.val.2.1 true).length+4)) ≤
        N*roundPolynomial.eval N+7*N+2*(N+1)^2+12 := by simp only [List.length_replicate]; omega
    simpa [timePolynomial,N] using bound
  · rw [input_word,initial]
    change RunsExactly (TM2.step (program actual)) _ _ _
    exact all

noncomputable def timed (x : Input) :
    TM2OutputsInTime (machine actual).computer (inputEncoding.encode x) (some (outputEncoding.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) where
  steps := Classical.choose (whole_run x)
  evals_in_steps := (Classical.choose_spec (whole_run x)).2
  steps_le_m := (Classical.choose_spec (whole_run x)).1
noncomputable def computes : Computes inputEncoding outputEncoding value where
  machine := machine actual
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C (machine actual).primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost (machine actual) (timed x).steps (some (initList (machine actual).computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right (machine actual).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

theorem output_length (x : Input) : (outputEncoding.encode (value x)).length≤2*((inputEncoding.encode x).length+1)^2+1 := by
  have hv := (input_bounds x).2.2.1
  have hb := children_bits_length x.val.1 x.val.2.1 0 x.val.2.2
  have hm := Nat.mul_le_mul hv (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) 2)
  change (framedListEncode UnaryBinary.unaryEncoding (value x)).length≤_
  rw [←bits_encode,List.length_append,List.length_singleton]
  change (bits (value x)).length≤x.val.2.2.length*(2*(0+x.val.2.2.length)+2) at hb
  nlinarith
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
