import Holant.Proofs.Tractability.AffineMachine.ResidueCells


namespace Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler

variable {A B C : Type} {ea : Encoding A Bool}

noncomputable def get (eb : Encoding B Bool) (d : B) {xs : A → List B} {i : A → ℕ}
    (list : Computes ea (framedListEncoding eb) xs) (index : Computes ea UnaryBinary.unaryEncoding i) :
    Computes ea eb (fun a => (xs a).getD (i a) d) :=
  (pairComputes list index).andThen (WireLists.getD eb d)

noncomputable def eqNat {f g : A → ℕ} (wf : Computes ea encodingNatBool f) (wg : Computes ea encodingNatBool g) :
    Computes ea encodingBoolBool (fun a => decide (f a = g a)) :=
  (pairComputes wf wg).andThen Endpoints.equalComputes

noncomputable def bool {f g : A → Bool} (op : Bool → Bool → Bool)
    (wf : Computes ea encodingBoolBool f) (wg : Computes ea encodingBoolBool g) :
    Computes ea encodingBoolBool (fun a => op (f a) (g a)) :=
  (pairComputes wf wg).andThen (ProductMachine.Rewrite.boolPairComputes (fun p => op p.1 p.2))

noncomputable def residue {f g : A → ZMod 4} (op : ZMod 4 → ZMod 4 → ZMod 4)
    (wf : Computes ea ResidueCells.encoding4 f) (wg : Computes ea ResidueCells.encoding4 g) :
    Computes ea ResidueCells.encoding4 (fun a => op (f a) (g a)) :=
  (pairComputes wf wg).andThen (ResidueCells.binary4 op)

noncomputable def flatMap (eb : Encoding B Bool) (ec : Encoding C Bool) (f : B → List C)
    (w : Computes eb (framedListEncoding ec) f) :
    Computes (framedListEncoding eb) (framedListEncoding ec) (List.flatMap f) :=
  congrComputes ((WireLists.mapComputes eb (framedListEncoding ec) f w).andThen (WireLists.flatten ec))
    (fun xs => by simp [List.flatMap_def])

noncomputable def map {xs : A → List B} (eb : Encoding B Bool) (ec : Encoding C Bool)
    (list : Computes ea (framedListEncoding eb) xs) (f : A → B → C)
    (cell : Computes (pairEncoding ea eb) ec (fun x => f x.1 x.2)) :
    Computes ea (framedListEncoding ec) (fun a => (xs a).map (f a)) :=
  (pairComputes (identityComputes ea) list).andThen (mapListComputes ea eb ec f cell)

noncomputable def unaryAdd : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    UnaryBinary.unaryEncoding (fun x => x.1 + x.2) :=
  recode (joinComputes
    ((Wiring.firstComputes _ _).andThen (encodeComputes UnaryBinary.unaryEncoding))
    ((Wiring.secondComputes _ _).andThen (encodeComputes UnaryBinary.unaryEncoding))) id (fun _ => rfl)
    (fun x => by
      change List.replicate x.1 true ++ List.replicate x.2 true = List.replicate (x.1+x.2) true
      exact (List.replicate_add _ _ _).symm)

end Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms
