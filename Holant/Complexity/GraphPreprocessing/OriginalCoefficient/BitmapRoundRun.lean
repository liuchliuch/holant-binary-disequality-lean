import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundStep

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
local instance : DecidableEq neighborMachine.K := neighborMachine.decidableK
local instance : DecidableEq (Stack neighborMachine) := (machine neighborMachine).decidableK

/-- Descending physical indexes prepend new bits in original vertex order.
Every neighbor call sees the same old bitmap, independent of earlier outputs. -/
theorem prefix_run (x : Input) (n : ℕ) (hn : n≤x.1.length) (output : List Bool) :
    ∃ k, k≤n*roundPolynomial.eval (inputEncoding.encode x).length ∧
      RunsExactly (TM2.step (program neighborMachine))
        (ready neighborMachine (phase neighborMachine 4) x.1 (x.1.take n).reverse
          (List.replicate n true) (edges x) output [])
        (ready neighborMachine (phase neighborMachine 4) x.1 [] [] (edges x) ((value x).take n++output) []) k := by
  induction n generalizing output with
  | zero => exact ⟨0,by simp,rfl⟩
  | succ n ih =>
    have hi : n<x.1.length := by omega
    have hnn : n≤x.1.length := by omega
    let i : Fin x.1.length := ⟨n,hi⟩
    have hcursor : (x.1.take (n+1)).reverse = x.1.get i::(x.1.take n).reverse := by
      rw [List.take_succ_eq_append_getElem hi]
      simp [i,List.get_eq_getElem]
    have hiv : n<(value x).length := by simpa using hi
    have hvalue : (value x).take (n+1) = (value x).take n++[bit x i] := by
      rw [List.take_succ_eq_append_getElem hiv]
      simp [value,i]
    obtain ⟨a,ha,first⟩ := vertex_run x i (x.1.take n).reverse output
    obtain ⟨b,hb,rest⟩ := ih hnn (bit x i::output)
    refine ⟨b+a,?_,?_⟩
    · nlinarith
    · have all := first.trans rest
      simpa only [hcursor,hvalue,List.replicate_succ,List.append_assoc,List.singleton_append,Fin.val_mk] using all

noncomputable def timePolynomial : Polynomial ℕ := Polynomial.X*roundPolynomial+3*Polynomial.X+12

/-- Whole actual clean synchronous round, with the loop bound physically
allocated from the input bitmap and all copies, frames and cleanup charged. -/
theorem whole_run (x : Input) :
    ∃ n, n≤timePolynomial.eval (inputEncoding.encode x).length ∧
      RunsExactly (machine neighborMachine).computer.step
        (initList (machine neighborMachine).computer (inputEncoding.encode x))
        (haltList (machine neighborMachine).computer (value x)) n := by
  have prep := prepare neighborMachine x.1 (edges x)
  obtain ⟨n,hn,loop⟩ := prefix_run x x.1.length (le_refl _) []
  have hv : (value x).take x.1.length = value x := by rw [← value_length x,List.take_length]
  simp only [List.take_length,hv,List.append_nil] at loop
  have last := finish neighborMachine x.1 (edges x) (value x)
  have all := (prep.trans loop).trans last
  refine ⟨(x.1.length+(edges x).length+5)+(n+(4*x.1.length+2*(edges x).length+7)),?_,?_⟩
  · have hB := table_length_le x
    have hm := Nat.mul_le_mul_right (roundPolynomial.eval (inputEncoding.encode x).length) hB
    have hlen : (inputEncoding.encode x).length=2*x.1.length+1+(edges x).length := by
      simp only [input_word,List.length_append,Holant.Algebraic.frame_length]
    have bound : (x.1.length+(edges x).length+5)+(n+(4*x.1.length+2*(edges x).length+7)) ≤
        (inputEncoding.encode x).length*roundPolynomial.eval (inputEncoding.encode x).length+3*(inputEncoding.encode x).length+12 := by omega
    simpa [timePolynomial] using bound
  · rw [initial]
    change RunsExactly (TM2.step (program neighborMachine)) _ _ _
    simpa only [input_word] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
