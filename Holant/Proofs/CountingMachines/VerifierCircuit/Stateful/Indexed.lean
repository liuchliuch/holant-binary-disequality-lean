import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Blocks
import Holant.Proofs.CountingMachines.VerifierCircuit.Support.ContextWordTableRun

set_option backward.isDefEq.respectTransparency false

/-!
# Physical indexed block traversal and exact uniform-cost gather order

Ported reference proof. See the task validation reports.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding

variable {B : Type}

/-- Traverse every encoded element, executing the supplied finite subprogram.
This is an internal composition combinator; concrete instances below supply
their own proved machines, not an assumed verifier compiler. -/
def flatMapComputes (e : Encoding B Bool) (f : B → List Bool) (w : Computes e Frame.wordEncoding f) :
    Computes (framedListEncoding e) Frame.wordEncoding (fun xs => xs.flatMap f) := by
  let provider : Computes (sigmaEncoding Frame.wordEncoding (fun _ => e)) Frame.wordEncoding
      (fun x => f x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding e).andThen w)
      (fun x => (x.1, x.2)) (fun _ => rfl) (fun _ => rfl)
  let prepare : Computes (framedListEncoding e)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => e))
      (fun xs => (⟨[], xs⟩ : Σ _ : List Bool, List B)) :=
    recode (pairComputes (constantComputes (framedListEncoding e) Frame.wordEncoding [])
      (identityComputes (framedListEncoding e))) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => e) _ provider)

def countComputes (e : Encoding B Bool) :
    Computes (framedListEncoding e) RuntimeParameters.unary (fun xs => xs.length) :=
  recode (flatMapComputes e (fun _ => [true]) (constantComputes e Frame.wordEncoding [true]))
    id (fun _ => rfl) (fun xs => by
      change xs.flatMap (fun _ => [true]) = List.replicate xs.length true
      induction xs with
      | nil => rfl
      | cons b xs ih => simp [ih, List.replicate_succ])

def flattenComputes : Computes (framedListEncoding Frame.wordEncoding) Frame.wordEncoding List.flatten :=
  congrComputes (flatMapComputes Frame.wordEncoding id (identityComputes Frame.wordEncoding))
    (fun xs => by simp)

abbrev Query (B : Type) := Σ xs : List B, Fin xs.length
def queryEncoding (e : Encoding B Bool) : Encoding (Query B) Bool :=
  Support.ContextWordTable.queryEncoding (framedListEncoding e) List.length

def words (f : Query B → List Bool) (xs : List B) : List Bool :=
  (List.ofFn (fun i : Fin xs.length => f ⟨xs, i⟩)).flatten

def wordsComputes (e : Encoding B Bool) (f : Query B → List Bool)
    (w : Computes (queryEncoding e) Frame.wordEncoding f) :
    Computes (framedListEncoding e) Frame.wordEncoding (words f) := by
  let table := Support.ContextWordTable.computes
    (size := List.length)
    (fun xs : List B => le_trans (by omega : xs.length ≤ 2 * xs.length + 1)
      (framedListEncoding_length_lower e xs)) (countComputes e) w
  refine congrComputes (table.andThen flattenComputes) ?_
  intro xs
  simp [words, Support.ContextWordTable.rows, List.ofFn_eq_map]

def selectedComputes (e : Encoding B Bool) :
    Computes (queryEncoding e) e (fun x => x.1.get x.2) := ParentRowSelect.computes e

def indexComputes (e : Encoding B Bool) :
    Computes (queryEncoding e) encodingNatBool (fun x => x.2.val) :=
  recode ((Wiring.secondComputes (framedListEncoding e) RuntimeParameters.unary).andThen UnaryBinary.computes)
    (fun x => (x.1, x.2.val)) (fun _ => rfl) (fun _ => rfl)

/-- At index i the original input has shifted by exactly g*i gates. This
proved closed form allows indexed physical providers to compile a gather. -/
theorem gather_rows {I J : Type} (p : J → Rows.Run I Unit) (g : ℕ)
    (hp : ∀ j env, (p j env).1.length = g) (xs : List J) (env : I → ℕ) :
    (Rows.gather p xs env).1 =
      (List.ofFn (fun i : Fin xs.length => (p (xs.get i) (Rows.shift (g * i.val) env)).1)).flatten := by
  induction xs generalizing env with
  | nil => rfl
  | cons j xs ih =>
    simp only [Rows.gather, Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route,
      List.append_nil, hp, List.ofFn_succ, List.flatten_cons, Fin.val_zero,
      Nat.mul_zero, Fin.val_succ, List.get_cons_zero, List.get_cons_succ']
    rw [ih]
    congr 2
    apply congrArg List.ofFn
    funext i
    congr 2
    funext a
    simp [Rows.shift, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed
