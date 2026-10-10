import Holant.Proofs.Algorithms.TransformRecognition.ProductVariableLayout
import Holant.Proofs.Algorithms.TransformRecognition.SparseTransform


namespace Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineVariableLayout
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)
abbrev Parameters := Σ j : Slot s, Fin (slotArity arity j) → Bool

def catalogue : List (Parameters arity) :=
  (ProductVariableLayout.slots s).flatMap (fun j =>
    (SparseTransform.allWords (slotArity arity j)).map (fun x => ⟨j,x⟩))

theorem mem_catalogue (p : Parameters arity) : p ∈ catalogue arity :=
  List.mem_flatMap.mpr ⟨p.1,ProductVariableLayout.mem_slots p.1,
    List.mem_map.mpr ⟨p.2,SparseTransform.mem_allWords p.2,rfl⟩⟩

def address (p : Parameters arity) : Fin (catalogue arity).length :=
  ⟨(catalogue arity).idxOf p,List.idxOf_lt_length_iff.mpr (mem_catalogue arity p)⟩

@[simp] theorem get_address (p : Parameters arity) :
    (catalogue arity).get (address arity p) = p := List.idxOf_get _

abbrev Count := (catalogue arity).length + (catalogue arity).length
abbrev Width := 5+Count arity

def scalar (p : Parameters arity) : Fin (Width arity) :=
  Fin.natAdd 5 (Fin.castAdd (catalogue arity).length (address arity p))
def reciprocal (p : Parameters arity) : Fin (Width arity) :=
  Fin.natAdd 5 (Fin.natAdd (catalogue arity).length (address arity p))

theorem scalar_reciprocal_ne (p q : Parameters arity) : scalar arity p ≠ reciprocal arity q := by
  intro h
  have he := congrArg Fin.val h
  have hp := (address arity p).isLt
  simp only [scalar,reciprocal,Fin.val_natAdd,Fin.val_castAdd] at he
  omega

def point {E : Type*} (z : Fin (Width arity) → E) :
    SymbolicTransform.Variables (Parameters arity) → E :=
  Sum.elim (fun j => z (Fin.castAdd (Count arity) j)) (fun p => z (scalar arity p))

/-- Runtime assignment is not needed to generate equations. This explicit
map is used to prove completeness from a source solution and its inverses. -/
def unpoint {E : Type*} (y : SymbolicTransform.Variables (Parameters arity) → E)
    (inv : Parameters arity → E) : Fin (Width arity) → E :=
  Fin.addCases (fun j => y (.inl j))
    (Fin.addCases (fun j => y (.inr ((catalogue arity).get j)))
      (fun j => inv ((catalogue arity).get j)))

@[simp] theorem point_unpoint {E : Type*}
    (y : SymbolicTransform.Variables (Parameters arity) → E) (inv : Parameters arity → E) :
    point arity (unpoint arity y inv) = y := by
  funext j
  cases j with
  | inl j => simp [point,unpoint]
  | inr p =>
    simp only [point,Sum.elim_inr,scalar,unpoint,Fin.addCases_right,
      Fin.addCases_left,get_address]

@[simp] theorem unpoint_reciprocal {E : Type*}
    (y : SymbolicTransform.Variables (Parameters arity) → E)
    (inv : Parameters arity → E) (p : Parameters arity) :
    unpoint arity y inv (reciprocal arity p) = inv p := by
  simp only [unpoint,reciprocal,Fin.addCases_right,get_address]

end Holant.LocalDrafts.MainChain.TransformRecognition.LocalAffineVariableLayout
