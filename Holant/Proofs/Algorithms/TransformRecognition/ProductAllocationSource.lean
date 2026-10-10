import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalProductSystem
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ProductAllocationSource
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open ProductAllocationMachine
variable {s : ℕ} (arity : Fin s → ℕ)

/-- A dependent flattened catalogue puts a parameter after exactly the sizes
of the preceding slots. Repeated outer slots are harmless: both lookups use
the first occurrence. This is the address invariant consumed by P rows. -/
theorem dependent_catalogue_index {A : Type} {B : A → Type}
    [DecidableEq A] [BEq A] [LawfulBEq A]
    [∀ a, DecidableEq (B a)] [∀ a, BEq (B a)] [∀ a, LawfulBEq (B a)]
    (xs : List A) (entries : (a : A) → List (B a)) (j : A) (p : B j)
    (hj : j ∈ xs) (hp : p ∈ entries j) :
    (xs.flatMap (fun a => (entries a).map (fun b => (⟨a,b⟩ : Sigma B)))).idxOf ⟨j,p⟩ =
      ((xs.take (xs.idxOf j)).map (fun a => (entries a).length)).sum +
        (entries j).idxOf p := by
  induction xs with
  | nil => simp at hj
  | cons a xs ih =>
    by_cases h : a = j
    · subst a
      rw [List.flatMap_cons, List.idxOf_append_of_mem
        (List.mem_map.mpr ⟨p,hp,rfl⟩)]
      rw [OriginalCatalogueSource.idxOf_map_injective
        (fun b => (⟨j,b⟩ : Sigma B)) (fun _ _ he => by cases he; rfl)]
      simp
    · have hn : (⟨j,p⟩ : Sigma B) ∉
          (entries a).map (fun b => (⟨a,b⟩ : Sigma B)) := by
        rintro he
        obtain ⟨b,_,he⟩ := List.mem_map.mp he
        exact h (congrArg Sigma.fst he)
      have hj' : j ∈ xs := (List.mem_cons.mp hj).resolve_left (Ne.symm h)
      rw [List.flatMap_cons, List.idxOf_append_of_notMem hn, List.length_map,
        ih hj']
      rw [List.idxOf_cons_ne xs h, List.take_succ_cons]
      simp only [List.map_cons,List.sum_cons]
      omega

theorem parameter_length (n : ℕ) : (ProductVariableLayout.parameters n).length=blockSize n := by
  simp only [ProductVariableLayout.parameters,List.length_cons,List.length_flatMap,
    List.length_cons,List.length_nil,List.map_const,List.length_finRange,List.sum_replicate,
    blockSize]
  simp only [List.map_const',List.length_finRange,List.sum_replicate, smul_eq_mul]
  simp only [Nat.zero_add,Nat.reduceAdd,Nat.mul_comm n 2, two_mul]

theorem count_source (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    count (OriginalFamilyPackingSource.fromSource arity input disequality).1 =
      OriginalProductSystem.Count arity := by
  simp only [count,sizes,OriginalFamilyPackingSource.fromSource,List.map_map,Function.comp_def,
    OriginalProductSystem.Count,ProductVariableLayout.catalogue,ProductVariableLayout.slots,
    List.length_flatMap,List.map_append,List.map_map,List.length_map,parameter_length,
    List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
    ProductVariableLayout.slotArity,Sum.elim_inl,Sum.elim_inr]
  simp only [List.length_map,parameter_length,blockSize]
  omega

/-- The lookup-prefix program really sums the preceding records, not an
unrelated table chosen from the mathematical layout. -/
theorem range_lookup_take {A B : Type} (xs : List A) (fallback : A) (f : A → B)
    (n : ℕ) (hn : n≤xs.length) :
    (List.range n).map (fun i => f (xs.getD i fallback))=(xs.take n).map f := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hn]
  · intro i hi hj
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    have hix : i<xs.length := lt_of_lt_of_le hin hn
    simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem xs fallback hix,List.getElem_take]

theorem prefix_spec (xs : Family) (i : ℕ) (hi : i≤xs.length) :
    prefixSize (xs,i) = ((sizes xs).take i).sum := by
  unfold prefixSize sizes
  rw [range_lookup_take xs (0,[]) (fun v => blockSize v.1) i hi,←List.map_take]

theorem edge_scalar_address (xs : Family) :
    scalarAddress (xs,xs.length)=count xs := by
  rw [scalarAddress,prefix_spec xs xs.length le_rfl]
  simp only [sizes,←List.map_take,List.take_length,count]
  omega

local instance slot_lawful : LawfulBEq (ProductVariableLayout.Slot s) where
  rfl := by
    intro a
    cases a <;> simp [BEq.beq,Sum.instBEq.beq]
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,Sum.instBEq.beq]

theorem slot_index (j : ProductVariableLayout.Slot s) :
    (ProductVariableLayout.slots s).idxOf j = OriginalCatalogueSource.slotNumber j := by
  cases j with
  | inl i =>
    rw [ProductVariableLayout.slots, List.idxOf_append_of_mem
      (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)]
    rw [OriginalCatalogueSource.idxOf_map_injective Sum.inl Sum.inl_injective]
    exact List.idxOf_finRange i
  | inr u =>
    have hn : (Sum.inr u : ProductVariableLayout.Slot s) ∉
        (List.finRange s).map Sum.inl := by simp
    rw [ProductVariableLayout.slots,List.idxOf_append_of_notMem hn]
    cases u
    simp [OriginalCatalogueSource.slotNumber]

theorem parameter_index (j : ProductVariableLayout.Slot s)
    (p : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Parameter
      (ProductVariableLayout.slotArity arity j)) :
    (ProductVariableLayout.address arity ⟨j,p⟩).val =
      (((ProductVariableLayout.slots s).take (OriginalCatalogueSource.slotNumber j)).map
        (fun k => blockSize (ProductVariableLayout.slotArity arity k))).sum +
      (ProductVariableLayout.parameters (ProductVariableLayout.slotArity arity j)).idxOf p := by
  change (ProductVariableLayout.catalogue arity).idxOf ⟨j,p⟩ = _
  have h := dependent_catalogue_index (ProductVariableLayout.slots s)
    (fun k => ProductVariableLayout.parameters (ProductVariableLayout.slotArity arity k)) j p
    (ProductVariableLayout.mem_slots j) (ProductVariableLayout.mem_parameters p)
  simpa only [ProductVariableLayout.catalogue,slot_index,parameter_length] using h

theorem scalar_prefix (input : OriginalFamilyInput.Input arity)
    (j : ProductVariableLayout.Slot s) :
    prefixSize (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j) =
      (((ProductVariableLayout.slots s).take (OriginalCatalogueSource.slotNumber j)).map
        (fun k => blockSize (ProductVariableLayout.slotArity arity k))).sum := by
  have hj : OriginalCatalogueSource.slotNumber j ≤ s := by
    cases j with
    | inl i => exact Nat.le_of_lt i.isLt
    | inr u => exact le_rfl
  rw [prefix_spec _ _ (by simpa only [OriginalCatalogueSource.family_length] using hj)]
  unfold ProductVariableLayout.slots
  rw [List.take_append_of_le_length (by simpa only [List.length_map,List.length_finRange] using hj)]
  simp only [sizes,OriginalCatalogueSource.family,OriginalFamilyPackingSource.fromSource,
    ←List.map_take,List.map_map,Function.comp_def,ProductVariableLayout.slotArity,Sum.elim_inl]

theorem scalar_source (input : OriginalFamilyInput.Input arity)
    (j : ProductVariableLayout.Slot s) :
    scalarAddress (OriginalCatalogueSource.family arity input,OriginalCatalogueSource.slotNumber j) =
      (OriginalProductSystem.parameterVariable arity ⟨j,none⟩).val := by
  rw [scalarAddress,scalar_prefix]
  simp only [OriginalProductSystem.parameterVariable,OriginalVariableLayout.parameter,
    Fin.val_castAdd,Fin.val_natAdd]
  rw [parameter_index]
  simp [ProductVariableLayout.parameters]

theorem unary_flat_index {n : ℕ} (xs : List (Fin n)) (j : Fin n) (b : Bool)
    (hj : j ∈ xs) :
    (xs.flatMap (fun k => [some (k,false),some (k,true)])).idxOf (some (j,b)) =
      xs.idxOf j + xs.idxOf j + (if b then 1 else 0) := by
  induction xs with
  | nil => simp at hj
  | cons k xs ih =>
    by_cases h : k=j
    · subst k
      cases b <;> simp [List.flatMap_cons,List.idxOf_cons]
    · have hf : some (k,false) ≠ some (j,b) := by
        intro he
        exact h (congrArg Prod.fst (Option.some.inj he))
      have ht : some (k,true) ≠ some (j,b) := by
        intro he
        exact h (congrArg Prod.fst (Option.some.inj he))
      have hj' : j ∈ xs := (List.mem_cons.mp hj).resolve_left (Ne.symm h)
      simp only [List.flatMap_cons,List.cons_append,List.nil_append]
      rw [List.idxOf_cons_ne _ hf,List.idxOf_cons_ne _ ht,ih hj',List.idxOf_cons_ne _ h]
      omega

theorem unary_parameter_index {n : ℕ} (j : Fin n) (b : Bool) :
    (ProductVariableLayout.parameters n).idxOf (some (j,b)) =
      1+j.val+j.val+(if b then 1 else 0) := by
  rw [ProductVariableLayout.parameters,List.idxOf_cons_ne _ (by simp),
    unary_flat_index _ j b (List.mem_finRange j),List.idxOf_finRange]
  omega

theorem unary_source (input : OriginalFamilyInput.Input arity)
    (k : ProductVariableLayout.Slot s) (j : Fin (ProductVariableLayout.slotArity arity k)) :
    unaryPair (scalarAddress (OriginalCatalogueSource.family arity input,
      OriginalCatalogueSource.slotNumber k),j.val) =
      ((OriginalProductSystem.parameterVariable arity ⟨k,some (j,false)⟩).val,
       (OriginalProductSystem.parameterVariable arity ⟨k,some (j,true)⟩).val) := by
  rw [scalarAddress,scalar_prefix]
  simp only [unaryPair,OriginalProductSystem.parameterVariable,OriginalVariableLayout.parameter,
    Fin.val_castAdd,Fin.val_natAdd,parameter_index,unary_parameter_index,Bool.false_eq_true,
    ite_false,ite_true]
  congr 1 <;> omega

theorem entry_address_source (input : OriginalFamilyInput.Input arity) (q : ℕ)
    (p : LocalAffineVariableLayout.Parameters arity) :
    OriginalCatalogueMachine.address (q,OriginalCatalogueMachine.catalogue
      (OriginalCatalogueSource.family arity input),OriginalCatalogueSource.key arity p) =
      (OriginalTensorRows.entryVariable arity q p.1 p.2).val := by
  rw [OriginalCatalogueSource.catalogue_exact]
  change 5+q+(List.map (OriginalCatalogueSource.key arity)
    (LocalAffineVariableLayout.catalogue arity)).idxOf (OriginalCatalogueSource.key arity p) = _
  rw [OriginalCatalogueSource.idxOf_map_injective (OriginalCatalogueSource.key arity)
    (OriginalCatalogueSource.key_injective arity)]
  simp only [OriginalTensorRows.entryVariable,OriginalAffineSystem.entryIndex,
    OriginalVariableLayout.original,LocalAffineVariableLayout.address,
    Fin.val_natAdd,Fin.val_castAdd]
  change 5+q+(LocalAffineVariableLayout.catalogue arity).idxOf p =
    5+(q+(LocalAffineVariableLayout.catalogue arity).idxOf p)
  omega

theorem entry_table_source (input : OriginalFamilyInput.Input arity) (q : ℕ)
    (j : ProductVariableLayout.Slot s) :
    OriginalAddressTablesMachine.table (OriginalCatalogueSource.family arity input,q,
      OriginalCatalogueSource.slotNumber j) =
      (SparseTransform.allWords (ProductVariableLayout.slotArity arity j)).map
        (fun x => RationalTensorMachine.wireRow (x,OriginalTensorRows.entryVariable arity q j x)) := by
  simp only [OriginalAddressTablesMachine.table,OriginalCatalogueSource.atVertex_exact,
    List.map_map,Function.comp_def,OriginalCatalogueSource.key,RationalTensorMachine.wireRow]
  apply List.map_congr_left
  intro x _
  congr 1
  exact entry_address_source arity input q ⟨j,x⟩

theorem width_source (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    OriginalAllocatedPackingMachine.width
      (OriginalFamilyPackingSource.fromSource arity input disequality,
        count (OriginalFamilyPackingSource.fromSource arity input disequality).1) =
      OriginalProductSystem.Width arity := by
  rw [count_source,OriginalAllocatedPackingMachine.width_source]

end Holant.LocalDrafts.MainChain.TransformRecognition.ProductAllocationSource
