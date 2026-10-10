import Holant.Proofs.Traversal.ArityTwo.RootPort


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RunComposition
open Holant.Complexity Computability BinaryCompose FixedFieldMachines
open GraphPreprocessing
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem andThen_machine {A B C : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {ec : Encoding C Bool} {f : A → B} {g : B → C}
    (u : Computes ea eb f) (v : Computes eb ec g) :
    (u.andThen v).machine = u.machine.compose v.machine := rfl

def restricted {A : Type} (e : Encoding A Bool) (P : A → Prop) [DecidablePred P] :
    Encoding {a // P a} Bool where
  encode a := e.encode a.val
  decode bits := do
    let a ← e.decode bits
    if h : P a then some ⟨a,h⟩ else none
  decode_encode a := by simp [a.property]

def timePolynomial {A : Type} {ea : Encoding A Bool} {input : A → List Bool}
    (w : Computes ea Frame.wordEncoding input) (p : Polynomial ℕ) : Polynomial ℕ :=
  w.time + (p+2*Polynomial.X+2).comp w.outputBound.bound

def computes {A : Type} {ea : Encoding A Bool} {input output : A → List Bool}
    (w : Computes ea Frame.wordEncoding input) (m : Machine) (p : Polynomial ℕ)
    (h : ∀ a, ∃ t, t ≤ p.eval (input a).length ∧
      (fun c => c.bind m.computer.step)^[t] (some (Turing.initList m.computer (input a))) =
        some (Turing.haltList m.computer (output a))) : Computes ea Frame.wordEncoding output where
  machine := w.machine.compose m
  time := timePolynomial w p
  outputs a := by
    let t := Classical.choose (h a)
    have ht := (Classical.choose_spec (h a)).1
    have hr := (Classical.choose_spec (h a)).2
    have run := Machine.compose_run w.machine m _ _ _ (w.outputs a).steps t
      (w.outputs a).evals_in_steps hr
    refine {
      steps := t+(2*((input a).length+1)+(w.outputs a).steps)
      evals_in_steps := run
      steps_le_m := ?_ }
    have hw := (w.outputs a).steps_le_m
    have hs := natPolynomial_eval_mono (p+2*Polynomial.X+2) (w.outputBound.length_le a)
    change (p+2*Polynomial.X+2).eval (input a).length ≤ _ at hs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat] at hs
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
      Polynomial.eval_X,Polynomial.eval_ofNat]
    omega

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RunComposition
