import Holant.Proofs.Algorithms.TransformRecognition.SymbolicTransform
import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Templates
import Mathlib.Data.List.FinRange


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ProductVariableLayout
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
variable {s : ℕ} (arity : Fin s → ℕ)
abbrev Slot (s : ℕ) := Fin s ⊕ Unit

def slotArity : Slot s → ℕ := Sum.elim arity (fun _ => 2)
abbrev Parameters := Σ j : Slot s, Parameter (slotArity arity j)

def slots (s : ℕ) : List (Slot s) :=
  (List.finRange s).map Sum.inl ++ [.inr ()]

def parameters (n : ℕ) : List (Parameter n) :=
  none :: (List.finRange n).flatMap (fun j => [some (j,false),some (j,true)])

def catalogue : List (Parameters arity) :=
  (slots s).flatMap (fun j => (parameters (slotArity arity j)).map (fun p => ⟨j,p⟩))

theorem mem_slots (j : Slot s) : j ∈ slots s := by
  cases j with
  | inl i => simp [slots]
  | inr u => cases u; simp [slots]

theorem mem_parameters {n : ℕ} (p : Parameter n) : p ∈ parameters n := by
  cases p with
  | none => simp [parameters]
  | some p =>
    obtain ⟨j,b⟩ := p
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨j,List.mem_finRange j,?_⟩
    cases b <;> simp

theorem mem_catalogue (p : Parameters arity) : p ∈ catalogue arity :=
  List.mem_flatMap.mpr ⟨p.1,mem_slots p.1,
    List.mem_map.mpr ⟨p.2,mem_parameters p.2,rfl⟩⟩

def address (p : Parameters arity) : Fin (catalogue arity).length :=
  ⟨(catalogue arity).idxOf p,List.idxOf_lt_length_iff.mpr (mem_catalogue arity p)⟩

@[simp] theorem get_address (p : Parameters arity) :
    (catalogue arity).get (address arity p) = p := List.idxOf_get _

theorem address_injective : Function.Injective (address arity) := by
  intro p q h
  have he := congrArg (fun i => (catalogue arity).get i) h
  simpa only [get_address] using he

def parameterVariable (p : Parameters arity) : Fin (5+(catalogue arity).length) :=
  Fin.natAdd 5 (address arity p)

def point {E : Type*} (z : Fin (5+(catalogue arity).length) → E) :
    SymbolicTransform.Variables (Parameters arity) → E :=
  Sum.elim (fun j => z (Fin.castAdd (catalogue arity).length j))
    (fun p => z (parameterVariable arity p))

def unpoint {E : Type*} (y : SymbolicTransform.Variables (Parameters arity) → E) :
    Fin (5+(catalogue arity).length) → E :=
  Fin.addCases (fun j => y (.inl j)) (fun k => y (.inr ((catalogue arity).get k)))

@[simp] theorem point_unpoint {E : Type*}
    (y : SymbolicTransform.Variables (Parameters arity) → E) :
    point arity (unpoint arity y) = y := by
  funext j
  cases j with
  | inl j => simp [point,unpoint]
  | inr p =>
    simp only [point,Sum.elim_inr,parameterVariable,unpoint,Fin.addCases_right,get_address]

end Holant.LocalDrafts.MainChain.TransformRecognition.ProductVariableLayout
