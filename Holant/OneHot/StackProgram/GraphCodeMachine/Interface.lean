import Holant.OneHot.StackProgram.GraphCodeMachine.Bounds
import Holant.Complexity.BinaryCompose.OutputBound

/-! Actual finite Boolean-stack compilers for prepared labelled trees and forests.
The source graph materializer remains a separate explicit input boundary. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ)
variable (hlabels : ∀ a, (e.encode a).length ≤ C)

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C (rate C) * Polynomial.X + Polynomial.C (overhead C)

noncomputable def treeComputes :
    BinaryCompose.Computes (TreeEncoding.treeEncoding e) (codeEncoding e) compileTree where
  machine := machine e C .tree
  time := timePolynomial C
  outputs t := {
    steps := treeTicks e t + ((codeEncoding e).encode (compileTree t)).length + 5
    evals_in_steps := compile_tree_exact e C hlabels t
    steps_le_m := by simpa [timePolynomial, TreeEncoding.treeEncoding] using tree_time_le e C hlabels t }

noncomputable def forestComputes :
    BinaryCompose.Computes (TreeEncoding.forestEncoding e) (codeEncoding e) compileForest where
  machine := machine e C .forest
  time := timePolynomial C
  outputs ts := {
    steps := forestTicks e ts + ((codeEncoding e).encode (compileForest ts)).length + 5
    evals_in_steps := compile_forest_exact e C hlabels ts
    steps_le_m := by simpa [timePolynomial, TreeEncoding.forestEncoding] using forest_time_le e C hlabels ts }

noncomputable def closedComputes :
    BinaryCompose.Computes (closedEncoding e) (codeEncoding e) (fun p => compileClosed p.1 p.2) where
  machine := machine e C .closed
  time := timePolynomial C
  outputs p := {
    steps := closedTicks e p.1 p.2 + ((codeEncoding e).encode (compileClosed p.1 p.2)).length + 5
    evals_in_steps := compile_closed_exact e C hlabels p.1 p.2
    steps_le_m := by simpa [timePolynomial, closedEncoding, FixedFieldMachines.pairEncoding,
      TreeEncoding.forestEncoding] using closed_time_le e C hlabels p.1 p.2 }

noncomputable def treeOutputBound :
    PolynomialOutputBound (TreeEncoding.treeEncoding e) (codeEncoding e) compileTree where
  bound := timePolynomial C
  length_le t := by
    have h := tree_time_le e C hlabels t
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, TreeEncoding.treeEncoding]
    omega

noncomputable def forestOutputBound :
    PolynomialOutputBound (TreeEncoding.forestEncoding e) (codeEncoding e) compileForest where
  bound := timePolynomial C
  length_le ts := by
    have h := forest_time_le e C hlabels ts
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, TreeEncoding.forestEncoding]
    omega

noncomputable def closedOutputBound :
    PolynomialOutputBound (closedEncoding e) (codeEncoding e) (fun p => compileClosed p.1 p.2) where
  bound := timePolynomial C
  length_le p := by
    have h := closed_time_le e C hlabels p.1 p.2
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, closedEncoding, FixedFieldMachines.pairEncoding, TreeEncoding.forestEncoding]
    omega

end Holant.OneHot.StackProgram.GraphCodeMachine
