import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChild
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildrenBounds

/-! Actual original-order child traversal with retained original cut context. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChildList
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := Σ x : ResidualContext.Query s b arity, List (Fin (ResidualContext.source x.1).val.vertices.length)
def indices (x : ResidualContext.Query s b arity) := OccurrenceLabel.unaryPortEncoding (ResidualContext.source x.1).val.vertices.length
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) := ContextFlatMap.inputEncoding (ResidualContext.queryEncoding s b arity) indices
def value (a z : Bool) (x : Input s b arity) := x.2.flatMap (fun child => ResidualActionChild.value a z ⟨x.1,child⟩)
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (value a z) :=
  ContextFlatMap.computes (ResidualContext.queryEncoding s b arity) indices (ResidualActionChild.value a z) (ResidualActionChild.computes a z s b arity)
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := ContextFlatMap.machine (ResidualActionChild.machine a z s b arity)
@[simp] theorem computes_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (computes a z s b arity).machine=machine a z s b arity := rfl
theorem inFP (a z : Bool) : InFP (inputEncoding s b arity) Frame.wordEncoding (value a z) := (computes a z s b arity).inFP

theorem index_encoding (n : ℕ) (xs : List (Fin n)) :
    framedListEncode UnaryBinary.unaryEncoding (xs.map Fin.val)=framedListEncode (OccurrenceLabel.unaryPortEncoding n) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,framedListEncode,ih]; rfl
def original (x : ResidualContext.Query s b arity) : Input s b arity :=
  ⟨x,ChildEnumerate.children ((ResidualContext.source x.1).val.graph (ResidualContext.source x.1).property) x.2⟩
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (inputEncoding s b arity) original :=
  recode (pairComputes (identityComputes (ResidualContext.queryEncoding s b arity)) ((ResidualContext.originalComputes s b arity).andThen (RawChildren.computes s b arity))) id
    (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _++framedListEncode UnaryBinary.unaryEncoding
        ((ChildEnumerate.children ((ResidualContext.source x.1).val.graph (ResidualContext.source x.1).property) x.2).map Fin.val)=_
      rw [index_encoding]
      rfl)
noncomputable def originalComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (fun x => value a z (original x)) :=
  (prepareComputes s b arity).andThen (computes a z s b arity)
abbrev originalMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine identityMachine (ResidualContext.originalMachine.compose RawChildren.machine)).compose (machine a z s b arity)
@[simp] theorem original_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    (originalComputes a z s b arity).machine=originalMachine a z s b arity := rfl
theorem original_inFP (a z : Bool) : InFP (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (fun x => value a z (original x)) :=
  (originalComputes a z s b arity).inFP

noncomputable def timePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (originalComputes a z s b arity).time.comp (7*(Polynomial.X+1))
noncomputable def timed (a z : Bool) (x : ResidualContext.Query s b arity) :
    TM2OutputsInTime (originalMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x)
      (some (value a z (original x))) ((timePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length) where
  steps := ((originalComputes a z s b arity).outputs x).steps
  evals_in_steps := ((originalComputes a z s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (originalComputes a z s b arity).time (ResidualContext.query_length x)
    exact le_trans ((originalComputes a z s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial a z s b arity*Polynomial.C (originalMachine a z s b arity).primitiveBudget
theorem primitive_bound (a z : Bool) (x : ResidualContext.Query s b arity) :
    primitiveCost (originalMachine a z s b arity) (timed a z x).steps
      (some (initList (originalMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x))) ≤
      (primitivePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  have h := Nat.mul_le_mul_right (originalMachine a z s b arity).primitiveBudget (timed a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

open Holant.OneHot.StackProgram.GraphLabelEncoding
theorem output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    (value a z (original x)).length≤(RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length+6) := by
  have hc := (ResidualContext.source x.1).val.counts_le_encoded_length
  have hn := ChildEnumerate.children_length_le ((ResidualContext.source x.1).val.graph (ResidualContext.source x.1).property) x.2
  have ho := ContextFlatMap.flat_length_bound (fun child => ResidualActionChild.value a z ⟨x,child⟩)
    (ChildEnumerate.children ((ResidualContext.source x.1).val.graph (ResidualContext.source x.1).property) x.2)
    (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length+6) (by
      intro child _
      have h := ResidualActionChild.output_length (s := s) (b := b) (arity := arity) a z ⟨x,child⟩
      dsimp only at h
      have hv := child.isLt
      change child.val<(ResidualContext.source x.1).val.vertices.length at hv
      omega)
  exact le_trans ho (Nat.mul_le_mul_right _ (by change _≤_; change _≤(ResidualContext.source x.1).val.vertices.length at hn; omega))
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChildList
