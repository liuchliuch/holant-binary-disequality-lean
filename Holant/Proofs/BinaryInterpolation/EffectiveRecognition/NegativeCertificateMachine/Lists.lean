import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Arithmetic


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Lists
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open CommonFieldMachine
open Holant.LocalDrafts.Tractability.AffineMachine

theorem succ_iterate (n : ℕ) : (Nat.succ^[n]) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]

noncomputable def toUnary : Executes encodingNatBool UnaryBinary.unaryEncoding id :=
  Executes.congr
    ((Executes.ofComputes (pairComputes (identityComputes encodingNatBool)
      (constantComputes encodingNatBool UnaryBinary.unaryEncoding 0))).comp
        (Iteration.executes UnaryBinary.unaryEncoding (Executes.ofComputes WireLists.succComputes)))
    succ_iterate

noncomputable def lookup {A : Type} (e : Encoding A Bool) (default : A) :
    Executes (pairEncoding (framedListEncoding e) encodingNatBool) e
      (fun p => p.1.getD p.2 default) :=
  (Executes.pair
    (Executes.ofComputes (Wiring.firstComputes (framedListEncoding e) encodingNatBool))
    ((Executes.ofComputes (Wiring.secondComputes (framedListEncoding e) encodingNatBool)).comp toUnary)).comp
      (Executes.ofComputes (WireLists.getD e default))

noncomputable def singleton {A : Type} (e : Encoding A Bool) :
    Computes e (framedListEncoding e) List.singleton :=
  recode (joinComputes (entryComputes e) (constantComputes e Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def map {A B C : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (ec : Encoding C Bool) {xs : A → List B} (list : Executes ea (framedListEncoding eb) xs)
    (f : A → B → C) (cell : Executes (pairEncoding ea eb) ec (fun p => f p.1 p.2)) :
    Executes ea (framedListEncoding ec) (fun a => (xs a).map (f a)) :=
  (Executes.pair (Executes.ofComputes (identityComputes ea)) list).comp
    (Executes.mapList ea eb ec f cell)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Lists
