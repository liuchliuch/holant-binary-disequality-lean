import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyInput


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyPackingSource
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalFamilyPackingMachine
variable {s : ℕ} (arity : Fin s → ℕ)

def fromSource (input : OriginalFamilyInput.Input arity) (disequality : Bool) : Input :=
  ((List.finRange s).map (fun i => (arity i,(SparseTransform.allWords (arity i)).map (input i))),disequality)

theorem ofFn_addCases {A : Type} {m n : ℕ} (f : Fin m → A) (g : Fin n → A) :
    List.ofFn (Fin.addCases f g) = List.ofFn f ++ List.ofFn g := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    have hi : i.castLE (Nat.le_add_right m n) = i.castAdd n := Fin.ext rfl
    rw [hi,Fin.addCases_left]
  · simp only [Fin.addCases_right]

def entryCode (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    LocalAffineVariableLayout.Parameters arity → RootCode
  | ⟨.inl i,x⟩ => input i x
  | ⟨.inr _,x⟩ => RationalRootCode.code (OriginalFamilyInput.edgeValue disequality (x (0 : Fin 2)) (x (1 : Fin 2)))

theorem pack_list (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    List.ofFn (OriginalFamilyInput.pack arity input disequality) =
      (LocalAffineVariableLayout.catalogue arity).map (entryCode arity input disequality) := by
  calc
    _ = (List.ofFn (LocalAffineVariableLayout.catalogue arity).get).map
        (entryCode arity input disequality) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

theorem original_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    original (fromSource arity input disequality) = List.ofFn (OriginalFamilyInput.pack arity input disequality) := by
  rw [pack_list]
  simp only [original,fromSource,LocalAffineVariableLayout.catalogue,ProductVariableLayout.slots,
    List.flatMap_map,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_flatMap,List.map_map,List.map_append,Function.comp_def,entryCode]
  cases disequality <;> rfl

theorem family_length (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    (fromSource arity input disequality).1.length=s := by simp only [fromSource,List.length_map,List.length_finRange]
theorem original_length (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    (original (fromSource arity input disequality)).length=OriginalAffineSystem.Entries arity := by
  rw [original_exact,List.length_ofFn]

theorem roots_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    roots (fromSource arity input disequality) = List.ofFn
      (OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input disequality)) := by
  rw [roots,original_exact]
  change _ = List.ofFn (Fin.addCases (OriginalFamilyInput.pack arity input disequality) StandardRootCodes.descriptors)
  rw [ofFn_addCases]
  rfl

theorem width_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    width (fromSource arity input disequality) = OriginalAffineSystem.Width arity := by
  simp only [width,base,parameterCount,family_length,original_length,OriginalAffineSystem.Width,
    OriginalVariableLayout.Width,OriginalVariableLayout.Extra]
  omega

theorem binding_value (m q : ℕ) (i : Fin (m+2)) :
    (OriginalVariableLayout.binding m q i).val = 5+q+i.val := by
  induction i using Fin.addCases with
  | left i => simp [OriginalVariableLayout.binding,OriginalVariableLayout.original]; omega
  | right i => simp [OriginalVariableLayout.binding,OriginalVariableLayout.special]; omega

theorem addresses_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    addresses (fromSource arity input disequality) = List.ofFn
      (fun i => (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) (s+1) i).val) := by
  unfold addresses
  rw [original_length]
  change CommonFieldMachine.Coordinates.tab (OriginalAffineSystem.Entries arity+2)
    (fun j => base (fromSource arity input disequality)+j) = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  congr 1
  funext i
  simp only [binding_value,base,parameterCount,family_length]

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyPackingSource
