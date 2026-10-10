import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Frontend
import Holant.Proofs.CountingMachines.StandardMachine.Support.Tagged

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Consume the EXISTING generic tagged-stream parser and
instruction embedding on the internally produced frontend. The four-symbol
input/output alphabet is Bool ⊕ Bool; it is never equated with Bool. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Standard
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

def time : Polynomial ℕ :=
  3*Polynomial.X+3+(Frontend.computes w).time.comp (2*Polynomial.X+1)

/-- The source code/witness separator is physically parsed before the same
frontend program. Both stream orders and the empty-witness boundary survive. -/
def verifier : PolyTime
    (encodingProd (inputEncoding w) (encodingList Bool))
    (taggedBoolEncoding Bool) (paddedAccept w) where
  tm := Tagged.computer (Frontend.computes w).machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time w
  outputsFun p := by
    let c := Frontend.computes w
    let g := (inputEncoding w).encode p.1
    let bits := p.2
    let run := c.outputs p
    have ha := Tagged.parse_exact c.machine g bits
    have hb := Tagged.lift_run c.machine _ _ run.steps run.evals_in_steps
    rw [Tagged.lift_halt] at hb
    refine {
      steps := run.steps+(3*g.length+2*bits.length+3)
      evals_in_steps := ?_
      steps_le_m := ?_ }
    · change (Tagged.stepper c.machine)^[run.steps+(3*g.length+2*bits.length+3)]
        (some (initList (Tagged.computer c.machine)
          (List.map id ((encodingProd (inputEncoding w) (encodingList Bool)).encode p)))) =
        some (haltList (Tagged.computer c.machine)
          (List.map id ((taggedBoolEncoding Bool).encode (paddedAccept w p))))
      simp only [List.map_id]
      change (Tagged.stepper c.machine)^[run.steps+(3*g.length+2*bits.length+3)]
        (some (initList (Tagged.computer c.machine) (g.map Sum.inl++bits.map Sum.inr))) = _
      rw [Function.iterate_add_apply]
      exact (congrArg ((Tagged.stepper c.machine)^[run.steps]) ha).trans
        (by simpa [Frontend.dataEncoding,FixedFieldMachines.pairEncoding,g,bits,
          GraphPreprocessing.Frame.wordEncoding,encodingBoolBool,taggedBoolEncoding,encodeBool] using hb)
    · have hh : ((Frontend.dataEncoding w).encode p).length ≤ 2*(g.length+bits.length)+1 := by
        simp only [Frontend.dataEncoding,FixedFieldMachines.pairEncoding_length,g,bits,
          GraphPreprocessing.Frame.wordEncoding,id_eq]
        omega
      have ht := natPolynomial_eval_mono c.time hh
      have hs := run.steps_le_m
      have hn : ((encodingProd (inputEncoding w) (encodingList Bool)).encode p).length =
          g.length+bits.length := by simp [g,bits,encodingList]
      simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_one,hn]
      change run.steps+(3*g.length+2*bits.length+3) ≤
        3*(g.length+bits.length)+3+c.time.eval (2*(g.length+bits.length)+1)
      omega
  finiteAlphabets _ := inferInstanceAs (Fintype (Bool ⊕ Bool))

/-- Same f, same original polynomial, and a NEW faithful Boolean input codec.
The false-suffix bijection proves the counts at the NEW bit-length P(width*N). -/
def witness : SharpPWitness (inputEncoding w) f where
  witnessLength := w.witnessLength
  accept := paddedAccept w
  verifier := verifier w
  counts := padded_counts w

theorem inSharpP : InSharpP (inputEncoding w) f := ⟨witness w⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Standard
