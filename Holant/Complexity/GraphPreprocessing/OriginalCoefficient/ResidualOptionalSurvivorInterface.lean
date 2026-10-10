import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivorFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

noncomputable def timePolynomial (s : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  ResidualSurvivorQuery.timePolynomial s arity + 10*Polynomial.X+10

theorem ticks_le (x : Input s b arity) :
    ticks x ≤ (timePolynomial s arity).eval ((inputEncoding s b arity).encode x).length := by
  rcases x with ⟨r,v,parent⟩
  cases parent with
  | none =>
    have hn : ((inputEncoding s b arity).encode ⟨r,v,none⟩).length =
        2*(RawClosedNetwork.encoding.encode r.val).length+2*v.val+3 := by
      change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r.val) ++
        (Holant.Algebraic.frame (List.replicate v.val true) ++ [false])).length = _
      simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate,List.length_singleton]
      omega
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,hn,ticks]
    omega
  | some q =>
    let y : ResidualSurvivorQuery.Input s b arity := ⟨r,v,q⟩
    have hn : ((ResidualSurvivorQuery.inputEncoding s b arity).encode y).length ≤
        ((inputEncoding s b arity).encode ⟨r,v,some q⟩).length := by
      change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r.val) ++
        (Holant.Algebraic.frame (List.replicate v.val true) ++
          RawClosedNetwork.endpointEncoding.encode (q.1.val,q.2))).length ≤
        (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode r.val) ++
        (Holant.Algebraic.frame (List.replicate v.val true) ++
          true :: RawClosedNetwork.endpointEncoding.encode (q.1.val,q.2))).length
      simp only [List.length_append,List.length_cons]
      omega
    have hs := ResidualSurvivorQuery.ticks_le y
    have ht := natPolynomial_eval_mono (ResidualSurvivorQuery.timePolynomial s arity) hn
    change ResidualSurvivorQuery.ticks y+1 ≤ _
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding portBits where
  machine := machine
  time := timePolynomial s arity
  outputs x := {
    steps := ticks x
    evals_in_steps := exact_run x
    steps_le_m := ticks_le x }

theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding portBits := (computes s b arity).inFP

/-- The optional stored parent selects an original local port, or none at roots
and at vertices not incident with the stored endpoint. -/
def selected (x : Input s b arity) : Option (Fin (arity (x.1.val.vertices.get x.2.1).1)) := match x.2.2 with
  | none => none
  | some q => ResidualSurvivorQuery.selected ⟨x.1,x.2.1,q⟩

theorem selected_encode (x : Input s b arity) :
    (optionEncoding (OccurrenceLabel.unaryPortEncoding (arity (x.1.val.vertices.get x.2.1).1))).encode
      (selected x) = portBits x := by
  rcases x with ⟨r,v,parent⟩
  cases parent with
  | none => rfl
  | some q => exact ResidualSurvivorQuery.selected_encode ⟨r,v,q⟩

theorem output_length (x : Input s b arity) : (portBits x).length ≤ maxArity s arity+1 := by
  rcases x with ⟨r,v,parent⟩
  cases parent with
  | none => simp [portBits]
  | some q => exact ResidualSurvivorQuery.output_length ⟨r,v,q⟩

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivor
