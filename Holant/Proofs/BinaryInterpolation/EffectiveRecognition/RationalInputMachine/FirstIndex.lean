import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Codec


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.FirstIndex
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability
open Holant.LocalDrafts.Tractability.AffineMachine
open OriginalCoefficient

abbrev inputEncoding := pairEncoding rationalEncoding CommonFieldMachine.coordinatesEncoding
def bitmap (q : ℚ) (xs : List ℚ) : List Bool := (xs.map (fun a => decide (q=a))) ++ [true]
def scanInput (p : ℚ × List ℚ) : FirstTrue.Input := ⟨bitmap p.1 p.2,by simp [bitmap]⟩

theorem bitmap_index (q : ℚ) (xs : List ℚ) : (bitmap q xs).findIdx id=xs.idxOf q := by
  induction xs with
  | nil => simp [bitmap]
  | cons a xs ih =>
    by_cases h : a=q
    · subst a; simp [bitmap,List.findIdx_cons]
    · have h' : q≠a := Ne.symm h
      simpa [bitmap,List.findIdx_cons,List.idxOf_cons,h,h'] using congrArg Nat.succ ih

noncomputable def bitmapComputes : Computes inputEncoding (framedListEncoding encodingBoolBool)
    (fun p => p.2.map (fun a => decide (p.1=a))) :=
  mapListComputes rationalEncoding rationalEncoding encodingBoolBool
    (fun q a => decide (q=a)) (equalComputes rationalEncoding)

noncomputable def rawBits : Computes (framedListEncoding encodingBoolBool) Frame.wordEncoding id :=
  congrComputes (ProductMachine.Bytecode.flatMap encodingBoolBool _ (encodeComputes encodingBoolBool))
    (fun xs => by induction xs with
      | nil => rfl
      | cons b bs ih =>
        change b :: bs.flatMap encodingBoolBool.encode = b :: bs
        exact congrArg (List.cons b) ih)

noncomputable def prepare : Computes inputEncoding FirstTrue.inputEncoding scanInput :=
  recode (joinComputes (bitmapComputes.andThen rawBits)
    (constantComputes inputEncoding Frame.wordEncoding [true])) id (fun _ => rfl) (fun _ => rfl)

noncomputable def computes : Computes inputEncoding encodingNatBool (fun p => p.2.idxOf p.1) :=
  congrComputes ((prepare.andThen FirstTrue.computes).andThen UnaryBinary.computes)
    (fun p => bitmap_index p.1 p.2)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.FirstIndex
