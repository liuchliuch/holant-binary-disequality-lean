import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Compiler


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition

theorem scalar_injective : Function.Injective (fun v : Fin 1 → ℚ => v 0) := by
  intro a b h
  funext i
  fin_cases i
  exact h

theorem index_scalar (xs : List (Fin 1 → ℚ)) (v : Fin 1 → ℚ) :
    (xs.map (fun a => a 0)).idxOf (v 0)=xs.idxOf v := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=v
    · subst a; simp
    · have hzero : a 0≠v 0 := fun he => h (scalar_injective he)
      simpa [List.idxOf_cons,h,hzero] using congrArg Nat.succ ih

theorem coefficients_wire {n : ℕ} (S : List (Sparse.Poly n 1)) :
    coefficients (bodyWire S) =
      (SparseCoefficientInput.coefficients RationalCompiler.data S).map (fun v => v 0) := by
  simp [coefficients,bodyWire,rowWire,termWire,SparseCoefficientInput.coefficients,
    RationalCompiler.data,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

theorem count_wire {n : ℕ} (S : List (Sparse.Poly n 1)) :
    (coefficients (bodyWire S)).length=RationalInputSystem.count S := by
  rw [coefficients_wire,List.length_map]

theorem rationals_wire {n : ℕ} (S : List (Sparse.Poly n 1)) :
    List.ofFn (RationalInputSystem.rationals S)=coefficients (bodyWire S) := by
  rw [coefficients_wire]
  exact List.ofFn_getElem_eq_map (SparseCoefficientInput.coefficients RationalCompiler.data S)
      (fun v => v 0)

theorem target_wire {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    targets (fromSource original S address)=List.ofFn (RationalInputSystem.target original S) := by
  simp only [targets,fromSource]
  rw [← rationals_wire,List.map_ofFn]
  symm
  unfold RationalInputSystem.target OriginalCoefficientBindings.target
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    have he : i.castLE (Nat.le_add_right m (RationalInputSystem.count S)) =
        i.castAdd (RationalInputSystem.count S) := rfl
    rw [he,Fin.addCases_left]
  · congr 1
    funext i
    rw [Fin.addCases_right]
    rfl

theorem body_row_wire {n : ℕ} (m : ℕ) (S : List (Sparse.Poly n 1))
    (p : Sparse.Poly n 1) (hp : p ∈ S) :
    (rowWire p).map (bodyTerm m (coefficients (bodyWire S))) =
      NegativeCertificateMachine.equationWire (RationalInputSystem.shifted m S
        (SparseCoefficientInput.equation RationalCompiler.data S p hp)) := by
  simp [rowWire,termWire,bodyTerm,coefficients_wire,index_scalar,
    NegativeCertificateMachine.equationWire,NegativeCertificateMachine.sourceTermWire,
    RationalInputSystem.shifted,SparseCoefficientInput.equation,SparseCoefficientInput.index,
    List.map_map,Function.comp_def]
  exact (List.attach_map_val (l := p) (f := fun t : Sparse.Term n 1 =>
    (m+(SparseCoefficientInput.coefficients RationalCompiler.data S).idxOf t.2,List.ofFn t.1))).symm

theorem body_rows_wire {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    bodyRows (fromSource original S address) =
      NegativeCertificateMachine.systemWire (RationalInputSystem.equations m S) := by
  simp only [bodyRows,fromSource,List.length_ofFn,bodyWire,List.map_map,
    NegativeCertificateMachine.systemWire,RationalInputSystem.equations,
    SparseCoefficientInput.system]
  change S.map (fun p => (rowWire p).map (bodyTerm m (coefficients (bodyWire S)))) =
    S.attach.map (fun p => NegativeCertificateMachine.equationWire (RationalInputSystem.shifted m S
      (SparseCoefficientInput.equation RationalCompiler.data S p.1 p.2)))
  rw [← List.attach_map_val (l := S)
    (f := fun p => (rowWire p).map (bodyTerm m (coefficients (bodyWire S))))]
  apply List.map_congr_left
  intro p hp
  exact body_row_wire m S p.1 p.2

theorem zero_ofFn (n : ℕ) : zero n=List.ofFn (0 : Fin n → ℕ) :=
  (List.ofFn_const n (0 : ℕ)).symm
theorem hit_ofFn {n : ℕ} (j : Fin n) : hit n j.val=List.ofFn (EncodedGuard.hit j) := by
  rw [hit,show (List.range n).map (fun i => if i=j.val then 1 else 0) =
    List.ofFn (fun i : Fin n => if i.val=j.val then 1 else 0) from CommonFieldMachine.Coordinates.tab_ofFn _ _]
  congr 1
  funext i
  simp only [EncodedGuard.hit,Pi.add_apply,Fin.ext_iff]

theorem triple_ofFn {n : ℕ} (a b c : Fin n) :
    triple n a.val b.val c.val=List.ofFn (EncodedGuard.hit a+EncodedGuard.hit b+EncodedGuard.hit c) := by
  change CommonFieldMachine.Coordinates.tab n _ = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  congr 1
  funext i
  simp only [EncodedGuard.hit,Pi.add_apply,Fin.ext_iff]

def oneSlot {m n : ℕ} (S : List (Sparse.Poly n 1)) : Fin (m+RationalInputSystem.count S) :=
  Fin.natAdd m (SparseCoefficientInput.oneIndex RationalCompiler.data S)
def negSlot {m n : ℕ} (S : List (Sparse.Poly n 1)) : Fin (m+RationalInputSystem.count S) :=
  Fin.natAdd m (RationalInputSystem.negativeIndex S)

theorem binding_wire {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) (i : Fin m) :
    binding (fromSource original S address) i.val =
      NegativeCertificateMachine.equationWire
        (OriginalCoefficientBindings.row (RationalInputSystem.negativeIndex S) address i) := by
  have hget : (List.ofFn (fun j => (address j).val)).getD i.val 0=(address i).val := by
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp
  simp only [binding,fromSource,List.length_ofFn,hget,zero_ofFn,hit_ofFn,
    NegativeCertificateMachine.equationWire,OriginalCoefficientBindings.row,List.map_cons,List.map_nil,
    NegativeCertificateMachine.sourceTermWire,RationalInputSystem.negativeIndex,
    SparseCoefficientInput.negIndex,Fin.val_castAdd,Fin.val_natAdd]

theorem bindings_wire {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    bindings (fromSource original S address)=NegativeCertificateMachine.systemWire
      (OriginalCoefficientBindings.rows (RationalInputSystem.negativeIndex S) address) := by
  unfold bindings
  rw [show (fromSource original S address).original.length=m by simp [fromSource]]
  rw [show (List.range m).map (binding (fromSource original S address)) =
    List.ofFn (fun i : Fin m => binding (fromSource original S address) i.val) from
      CommonFieldMachine.Coordinates.tab_ofFn _ _]
  simp only [NegativeCertificateMachine.systemWire,OriginalCoefficientBindings.rows,List.map_map]
  rw [← List.ofFn_eq_map]
  congr 1
  funext i
  exact binding_wire original S address i

theorem guard_wire {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    guard (fromSource original S address)=NegativeCertificateMachine.equationWire
      (EncodedGuard.equation (k:=k) (oneSlot (m:=m) S) (negSlot (m:=m) S)) := by
  simp only [guard,fromSource,List.length_ofFn]
  have h₁ := triple_ofFn (Fin.castAdd k (4 : Fin 5)) (Fin.castAdd k (0 : Fin 5)) (Fin.castAdd k (3 : Fin 5))
  have h₂ := triple_ofFn (Fin.castAdd k (4 : Fin 5)) (Fin.castAdd k (1 : Fin 5)) (Fin.castAdd k (2 : Fin 5))
  change triple (5+k) 4 0 3 = _ at h₁
  change triple (5+k) 4 1 2 = _ at h₂
  rw [h₁,h₂,zero_ofFn]
  rfl

theorem request_fromSource {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    request (fromSource original S address) =
      NegativeCatalogueMachine.fromSource (RationalInputSystem.target original S)
        (EncodedGuard.augment (oneSlot (m:=m) S) (negSlot (m:=m) S)
          (RationalInputSystem.system S address)) 0 := by
  have ht := target_wire original S address
  have hg := guard_wire original S address
  have hb := bindings_wire original S address
  have hs := body_rows_wire original S address
  unfold request
  rw [ht,hg,hb,hs]
  simp only [fromSource,List.length_ofFn,count_wire,
    NegativeCatalogueMachine.fromSource,EncodedGuard.augment,RationalInputSystem.system,
    NegativeCertificateMachine.systemWire,List.map_cons,List.map_append]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
