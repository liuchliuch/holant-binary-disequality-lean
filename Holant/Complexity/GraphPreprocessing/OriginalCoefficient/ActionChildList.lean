import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildLinear
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildrenBounds

/-! The actual original-order child list is generated from raw bytes and then
physically traversed, producing one exact coefficient/reference action chunk
per selected child. No prepared child list is supplied to the raw entry. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildList
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := Σ x : RawRootReach.Input s b arity, List (Fin x.1.val.vertices.length)
def indices (x : RawRootReach.Input s b arity) := OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) := ContextFlatMap.inputEncoding (RawRootReach.inputEncoding s b arity) indices
def value (x : Input s b arity) := x.2.flatMap (fun child => ActionChild.value ⟨x.1,child⟩)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding value :=
  ContextFlatMap.computes (RawRootReach.inputEncoding s b arity) indices ActionChild.value (ActionChildLinear.computes s b arity)
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := ContextFlatMap.machine (ActionChildLinear.machine s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding value := (computes s b arity).inFP

theorem index_encoding (n : ℕ) (xs : List (Fin n)) :
    framedListEncode UnaryBinary.unaryEncoding (xs.map Fin.val)=framedListEncode (OccurrenceLabel.unaryPortEncoding n) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,framedListEncode,ih]; rfl
def original (x : RawRootReach.Input s b arity) : Input s b arity :=
  ⟨x,ChildEnumerate.children (x.1.val.graph x.1.property) x.2⟩
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (inputEncoding s b arity) original :=
  recode (pairComputes (identityComputes (RawRootReach.inputEncoding s b arity)) (RawChildren.computes s b arity)) id
    (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _++framedListEncode UnaryBinary.unaryEncoding
        ((ChildEnumerate.children (x.1.val.graph x.1.property) x.2).map Fin.val)=_
      rw [index_encoding]
      rfl)
noncomputable def originalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding (fun x => value (original x)) :=
  (prepareComputes s b arity).andThen (computes s b arity)
abbrev originalMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine identityMachine RawChildren.machine).compose (machine s b arity)
@[simp] theorem original_machine (s b : ℕ) (arity : ℕ → ℕ) :
    (originalComputes s b arity).machine=originalMachine s b arity := rfl
theorem original_inFP : InFP (RawRootReach.inputEncoding s b arity) Frame.wordEncoding (fun x => value (original x)) :=
  (originalComputes s b arity).inFP

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (originalComputes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (originalMachine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some (value (original x))) ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((originalComputes s b arity).outputs x).steps
  evals_in_steps := ((originalComputes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (originalComputes s b arity).time (RawRootReach.input_length_le_original x)
    exact le_trans ((originalComputes s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (originalMachine s b arity).primitiveBudget
theorem primitive_bound (x : RawRootReach.Input s b arity) :
    primitiveCost (originalMachine s b arity) (timed x).steps
      (some (initList (originalMachine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (originalMachine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

open Holant.OneHot.StackProgram.GraphLabelEncoding
theorem output_length (x : RawRootReach.Input s b arity) :
    (value (original x)).length≤(RawClosedNetwork.encoding.encode x.1.val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode x.1.val).length+6) := by
  have hc := x.1.val.counts_le_encoded_length
  have hn := ChildEnumerate.children_length_le (x.1.val.graph x.1.property) x.2
  have ho := ContextFlatMap.flat_length_bound (fun child => ActionChild.value ⟨x,child⟩)
    (ChildEnumerate.children (x.1.val.graph x.1.property) x.2)
    (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode x.1.val).length+6) (by
      intro child _
      have h := ActionChild.output_length (s := s) (b := b) (arity := arity) ⟨x,child⟩
      dsimp only at h
      have hv := child.isLt
      change child.val<x.1.val.vertices.length at hv
      omega)
  exact le_trans ho (Nat.mul_le_mul_right _ (by change _≤_; change _≤x.1.val.vertices.length at hn; omega))
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildList
