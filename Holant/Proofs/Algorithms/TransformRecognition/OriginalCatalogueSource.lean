import Holant.Proofs.Algorithms.TransformRecognition.OriginalAddressTablesMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCatalogueSource
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)

def slotNumber : Slot s → ℕ
  | .inl i => i.val
  | .inr _ => s

theorem slotNumber_injective : Function.Injective (slotNumber (s:=s)) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (Fin.ext h)
    | inr u => have hi := i.isLt; simp only [slotNumber] at h; omega
  | inr u =>
    cases b with
    | inl j => have hj := j.isLt; simp only [slotNumber] at h; omega
    | inr v => congr

def key (p : LocalAffineVariableLayout.Parameters arity) : OriginalCatalogueMachine.Key :=
  (slotNumber p.1,List.ofFn p.2)

theorem key_injective : Function.Injective (key arity) := by
  rintro ⟨j,x⟩ ⟨k,y⟩ h
  have hj : j=k := slotNumber_injective (congrArg Prod.fst h)
  subst k
  have hx : x=y := List.ofFn_injective (congrArg Prod.snd h)
  subst y
  rfl

/-- First-match index is preserved by an injective representation map,
including lists with repetitions and absent lookup keys. -/
theorem idxOf_map_injective {A B : Type} [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (x : A) :
    (xs.map f).idxOf (f x)=xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=x
    · subst a; simp
    · have h' : f a≠f x := fun he => h (hf he)
      simp only [List.map_cons,List.idxOf_cons,beq_iff_eq,h,h',if_false,ih]

theorem slots_numbers : (ProductVariableLayout.slots s).map slotNumber=List.range (s+1) := by
  simp only [ProductVariableLayout.slots,List.map_append,List.map_map,List.map_cons,List.map_nil,
    Function.comp_def,slotNumber]
  rw [←List.ofFn_eq_map]
  have h := CommonFieldMachine.Coordinates.tab_ofFn s (fun i => i)
  simp only [CommonFieldMachine.Coordinates.tab,List.map_id_fun] at h
  rw [←h,List.range_succ]
  simp

def family (input : OriginalFamilyInput.Input arity) : OriginalCatalogueMachine.Family :=
  (OriginalFamilyPackingSource.fromSource arity input false).1

theorem family_length (input : OriginalFamilyInput.Input arity) : (family arity input).length=s :=
  OriginalFamilyPackingSource.family_length arity input false

theorem selected_arity (input : OriginalFamilyInput.Input arity) (j : Slot s) :
    ((OriginalCatalogueMachine.extended (family arity input)).getD (slotNumber j) (0,[])).1 =
      slotArity arity j := by
  cases j with
  | inl i =>
    rw [OriginalCatalogueMachine.extended,List.getD_append _ _ _ _ (by simpa only [family_length,slotNumber] using i.isLt)]
    change (((List.finRange s).map (fun k => (arity k,(SparseTransform.allWords (arity k)).map (input k)))).getD i.val (0,[])).1 = arity i
    rw [←List.ofFn_eq_map]
    rw [Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn]
  | inr u =>
    rw [OriginalCatalogueMachine.extended,List.getD_append_right _ _ _ _ (by simp only [family_length,slotNumber]; exact le_rfl)]
    simp only [family_length,slotNumber,Nat.sub_self,List.getD_cons_zero,slotArity,Sum.elim_inr]

theorem atVertex_exact (input : OriginalFamilyInput.Input arity) (j : Slot s) :
    OriginalCatalogueMachine.atVertex (family arity input) (slotNumber j) =
      ((SparseTransform.allWords (slotArity arity j)).map (fun x => ⟨j,x⟩)).map (key arity) := by
  simp only [OriginalCatalogueMachine.atVertex,selected_arity,RationalTableMachine.words_eq,
    List.map_map,Function.comp_def,key]

theorem catalogue_exact (input : OriginalFamilyInput.Input arity) :
    OriginalCatalogueMachine.catalogue (family arity input) =
      (LocalAffineVariableLayout.catalogue arity).map (key arity) := by
  rw [OriginalCatalogueMachine.catalogue,family_length,←slots_numbers]
  simp only [List.flatMap_map,Function.comp_def,atVertex_exact,
    LocalAffineVariableLayout.catalogue,List.map_flatMap]

theorem address_exact (input : OriginalFamilyInput.Input arity)
    (p : LocalAffineVariableLayout.Parameters arity) :
    OriginalCatalogueMachine.address (s+1,OriginalCatalogueMachine.catalogue (family arity input),key arity p) =
      (OriginalAffineSystem.entryVariable arity p.1 p.2).val := by
  rw [catalogue_exact]
  change 5+(s+1)+(List.map (key arity) (LocalAffineVariableLayout.catalogue arity)).idxOf (key arity p) = _
  rw [idxOf_map_injective (key arity) (key_injective arity) (LocalAffineVariableLayout.catalogue arity) p]
  simp only [OriginalAffineSystem.entryVariable,OriginalAffineSystem.entryIndex,
    OriginalVariableLayout.original,LocalAffineVariableLayout.address,
    Fin.val_natAdd,Fin.val_castAdd]
  change 5+(s+1)+(LocalAffineVariableLayout.catalogue arity).idxOf p =
    5+((s+1)+(LocalAffineVariableLayout.catalogue arity).idxOf p)
  omega

theorem table_exact (input : OriginalFamilyInput.Input arity) (j : Slot s) :
    OriginalAddressTablesMachine.table (family arity input,s+1,slotNumber j) =
      (SparseTransform.allWords (slotArity arity j)).map
        (fun x => RationalTensorMachine.wireRow (x,OriginalAffineSystem.entryVariable arity j x)) := by
  simp only [OriginalAddressTablesMachine.table,atVertex_exact,List.map_map,Function.comp_def,
    key,RationalTensorMachine.wireRow]
  apply List.map_congr_left
  intro x _
  congr 1
  exact address_exact arity input ⟨j,x⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalCatalogueSource
