import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Bounds

/-! A genuine finite Boolean-stack compiler at the explicit prepared-component
boundary. This witness does not claim to materialize descriptors from a raw graph. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ)
variable (hlabels : ∀ x, (e.encode x).length ≤ C)

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C (totalRate C) * Polynomial.X + 15

/-- Exactly the existing GraphCode right-fold product syntax, in clean physical output. -/
noncomputable def computes : BinaryCompose.Computes (listEncoding e) (codeEncoding e) productCode where
  machine := driver e C
  time := timePolynomial C
  outputs ds := {
    steps := listTicks e ds + ds.length + ((codeEncoding e).encode (productCode ds)).length + 6
    evals_in_steps := run_exact e C hlabels ds
    steps_le_m := by simpa [timePolynomial] using total_time_le e C hlabels ds }

noncomputable def outputBound : PolynomialOutputBound (listEncoding e) (codeEncoding e) productCode where
  bound := timePolynomial C
  length_le ds := by
    have h := total_time_le e C hlabels ds
    simpa [timePolynomial] using
      (show ((codeEncoding e).encode (productCode ds)).length ≤
        totalRate C * ((listEncoding e).encode ds).length + 15 by omega)

/-- Source graph materializers may use any specification type whose actual output
is the literal descriptor-list codec; composition uses the genuine driver. -/
noncomputable def recodeComputes {X : Type} (input : Encoding X Bool)
    (prepare : X → List (Descriptor A))
    (hword : ∀ x, (listEncoding e).encode (prepare x) = input.encode x) :
    BinaryCompose.Computes input (codeEncoding e) (fun x => productCode (prepare x)) :=
  FixedFieldMachines.recode (computes e C hlabels) prepare hword (fun _ => rfl)

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
