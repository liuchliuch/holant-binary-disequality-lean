import Holant.Proofs.Recognition.RuntimeTensorRows
import Mathlib.Data.List.GetD

/-! Literal correspondence of runtime candidate offsets and slice words with
the typed shape reconstructed from that same generated accepted packet.
These proofs never supply a partition to the machine. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRowsSoundness
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open UniformTensorWitnessBranch (Metadata)
open RuntimeTensorCatalogue RuntimeTensorValidation
open TensorDecisionNormalization
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem map_range_eq_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) :=
  CommonFieldMachine.Coordinates.tab_ofFn n f

variable {n : ℕ} (m : Metadata) (generated : m ∈ catalogue n)
variable (oneHot : Bool) (accepted : valid (oneHot,n,m)=true)

local notation "cnt" => RuntimeTensorReification.count m
local notation "sz" => RuntimeTensorReification.arity m
local notation "prt" => RuntimeTensorReification.blockPorts m generated oneHot accepted
local notation "pvt" => RuntimeTensorReification.pivot m generated

theorem offset_eq_sum (i : Fin cnt) : RuntimeTensorRows.offset (m.1,i.val) =
    ∑j : Fin i.val, sz (Fin.castLE i.isLt.le j) := by
  unfold RuntimeTensorRows.offset
  rw [map_range_eq_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  exact List.getD_eq_get m.1 0 (Fin.castLE i.isLt.le j)

theorem pivot_ofFn : List.ofFn pvt = m.2.2 := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using (generated_bounds n m generated).2.2.2.2.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn]
    rfl

theorem block_ports (i : Fin cnt) : RuntimeTensorRows.block (m,i.val) =
    List.ofFn (fun j : Fin (sz i) => (prt ⟨i,j⟩).val) := by
  unfold RuntimeTensorRows.block
  rw [List.getD_eq_get m.1 0 i,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  let p : Fin m.2.1.length := Fin.cast (generated_bounds n m generated).2.2.1.symm
    (Fin.cast (RuntimeTensorReification.size_sum m oneHot accepted) (finSigmaFinEquiv ⟨i,j⟩))
  have hp : p.val=RuntimeTensorRows.offset (m.1,i.val)+j.val := by
    change (finSigmaFinEquiv ⟨i,j⟩).val = _
    rw [finSigmaFinEquiv_apply,offset_eq_sum]
  calc
    m.2.1.getD (RuntimeTensorRows.offset (m.1,i.val)+j.val) 0 = m.2.1.getD p.val 0 := by rw [hp]
    _ = m.2.1.get p := List.getD_eq_get m.2.1 0 p
    _ = (prt ⟨i,j⟩).val := (RuntimeTensorReification.blockPorts_raw m generated oneHot accepted i j).symm

theorem block_mem (i a : Fin cnt) (b : Fin (sz a)) :
    (prt ⟨a,b⟩).val ∈ RuntimeTensorRows.block (m,i.val) ↔ a=i := by
  rw [block_ports m generated oneHot accepted i,List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    have h := (prt).injective (Fin.ext hj)
    exact (congrArg Sigma.fst h).symm
  · rintro rfl
    exact ⟨b,rfl⟩

theorem sliceWord_ofFn (i : Fin cnt) (x : Fin n → Bool) :
    RuntimeTensorRows.sliceWord (m,i.val,List.ofFn x) =
      List.ofFn (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩))) := by
  unfold RuntimeTensorRows.sliceWord RuntimeTensorRows.slice
  rw [←pivot_ofFn m generated,List.length_ofFn,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  obtain ⟨⟨a,b⟩,rfl⟩ := (prt).surjective j
  simp only [PositiveCertificateMachine.getD_ofFn]
  have ht : RuntimeTensorValidation.member (prt ⟨a,b⟩).val (RuntimeTensorRows.block (m,i.val))=true ↔ a=i :=
    (member_correct _ _).trans (block_mem m generated oneHot accepted i a b)
  by_cases h : a=i
  · subst a
    rw [ht.mpr rfl,if_pos rfl,blockWord_same]
  · have hf : RuntimeTensorValidation.member (prt ⟨a,b⟩).val (RuntimeTensorRows.block (m,i.val))=false := by
      cases hh : RuntimeTensorValidation.member (prt ⟨a,b⟩).val (RuntimeTensorRows.block (m,i.val))
      · rfl
      · exact (h (ht.mp hh)).elim
    rw [hf,if_neg Bool.false_ne_true,blockWord_other _ _ _ _ _ _ h]

theorem block_weight (i : Fin cnt) (x : Fin n → Bool) :
    RuntimeTensorRows.weight (RuntimeTensorRows.block (m,i.val),List.ofFn x) =
      Holant.weight (fun j => x (prt ⟨i,j⟩)) := by
  simp only [RuntimeTensorRows.weight,block_ports m generated oneHot accepted i,
    List.map_ofFn,PositiveCertificateMachine.getD_ofFn,List.sum_ofFn,
    RuntimeTensorRows.bitNat,Holant.weight,Function.comp_def]

variable {q : ℕ}

/-- The proof-side reference keeps the original coefficient addresses. -/
def request (address : (Fin n → Bool) → Fin (5+(1+q))) : RuntimeTensorRows.Input :=
  (5+(1+q),n,m,(SparseTransform.allWords n).map (fun y => RationalTensorMachine.wireRow (y,address y)))

def entries (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) : Sparse.Poly (5+(1+q)) 1 :=
  SymbolicInputTable.vertex RationalCompiler.data (SparseTransform.inverse RationalCompiler.data (1+q))
    (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x

theorem value_wire (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) :
    RuntimeTensorRows.value (request m address) (List.ofFn x)=RationalInputMachine.rowWire (entries address x) :=
  RationalTensorMachine.dense_vertex_wire x address

theorem pivot_value_wire (address : (Fin n → Bool) → Fin (5+(1+q))) :
    RuntimeTensorRows.value (request m address) (RuntimeTensorRows.pivot (request m address)) =
      RationalInputMachine.rowWire (entries address pvt) := by
  change RuntimeTensorRows.value (request m address) m.2.2 = _
  rw [←pivot_ofFn m generated]
  exact value_wire m address pvt

theorem slice_value_wire (address : (Fin n → Bool) → Fin (5+(1+q))) (i : Fin cnt) (x : Fin n → Bool) :
    RuntimeTensorRows.sliceValue (request m address) i.val (List.ofFn x) =
      RationalInputMachine.rowWire (entries address (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩)))) := by
  change RuntimeTensorRows.value (request m address) (RuntimeTensorRows.sliceWord (m,i.val,List.ofFn x)) = _
  rw [sliceWord_ofFn m generated oneHot accepted]
  exact value_wire m address _

def typedRow (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) : Sparse.Poly (5+(1+q)) 1 :=
  Sparse.sub
    (Sparse.mul RationalCompiler.data (entries address pvt)
      (SparseTransform.product RationalCompiler.data (List.ofFn (fun i : Fin cnt =>
        entries address (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩)))))))
    (Sparse.mul RationalCompiler.data (entries address x)
      (SparseTransform.product RationalCompiler.data (List.ofFn (fun _ : Fin cnt => entries address pvt))))

theorem row_wire (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) :
    RuntimeTensorRows.row (request m address) (List.ofFn x)=
      RationalInputMachine.rowWire (typedRow m generated oneHot accepted address x) := by
  have hs : (List.range cnt).map (fun i => RuntimeTensorRows.sliceValue (request m address) i (List.ofFn x)) =
      (List.ofFn (fun i : Fin cnt => entries address
        (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩))))).map RationalInputMachine.rowWire := by
    rw [map_range_eq_ofFn,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact slice_value_wire m generated oneHot accepted address i x
  have hp : (List.range cnt).map (fun _ => RuntimeTensorRows.value (request m address)
      (RuntimeTensorRows.pivot (request m address))) =
      (List.ofFn (fun _ : Fin cnt => entries address pvt)).map RationalInputMachine.rowWire := by
    rw [map_range_eq_ofFn,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact pivot_value_wire m generated address
  unfold RuntimeTensorRows.row
  change RationalSparseMachine.sub
    (RationalSparseMachine.mul _ (RationalSparseMachine.product (5+(1+q)) ((List.range cnt).map _)))
    (RationalSparseMachine.mul _ (RationalSparseMachine.product (5+(1+q)) ((List.range cnt).map _))) = _
  rw [hs,hp,pivot_value_wire m generated address,value_wire m address x,
    RationalSparseMachine.product_wire,RationalSparseMachine.product_wire,
    RationalSparseMachine.mul_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire]
  rfl

def typedGuard (address : (Fin n → Bool) → Fin (5+(1+q))) : Sparse.Poly (5+(1+q)) 1 :=
  Sparse.sub (Sparse.mul RationalCompiler.data (entries address pvt)
    (SparseTransform.variableCode RationalCompiler.data (Fin.natAdd 5 (0 : Fin (1+q)))))
    (Sparse.one RationalCompiler.data)

theorem guard_wire (address : (Fin n → Bool) → Fin (5+(1+q))) :
    RuntimeTensorRows.guard (request m address)=RationalInputMachine.rowWire (typedGuard m generated address) := by
  unfold RuntimeTensorRows.guard
  rw [pivot_value_wire m generated address]
  have hv := RationalSparseMachine.variable_wire (Fin.natAdd 5 (0 : Fin (1+q)))
  change RationalSparseMachine.variable (5+(1+q)) 5 = _ at hv
  change RationalSparseMachine.sub (RationalSparseMachine.mul _
    (RationalSparseMachine.variable (5+(1+q)) 5)) (RationalSparseMachine.one (5+(1+q))) = _
  rw [hv,RationalSparseMachine.mul_wire,RationalSparseMachine.one_wire,RationalSparseMachine.sub_wire]
  rfl

def typedSupport (address : (Fin n → Bool) → Fin (5+(1+q))) (i : Fin cnt) (x : Fin n → Bool) :
    Sparse.Poly (5+(1+q)) 1 :=
  if RuntimeTensorRows.highWeight (Holant.weight (fun j => x (prt ⟨i,j⟩))) then
    entries address (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩))) else []

theorem support_wire (address : (Fin n → Bool) → Fin (5+(1+q))) (i : Fin cnt) (x : Fin n → Bool) :
    RuntimeTensorRows.support (request m address) (i.val,List.ofFn x)=
      RationalInputMachine.rowWire (typedSupport m generated oneHot accepted address i x) := by
  unfold RuntimeTensorRows.support
  change (if RuntimeTensorRows.highWeight (RuntimeTensorRows.weight (RuntimeTensorRows.block (m,i.val),List.ofFn x)) then
    RuntimeTensorRows.sliceValue (request m address) i.val (List.ofFn x) else []) = _
  rw [block_weight m generated oneHot accepted i x]
  unfold typedSupport
  split <;> simp only [slice_value_wire m generated oneHot accepted address i x,RationalInputMachine.rowWire,List.map_nil]

def typedRows (address : (Fin n → Bool) → Fin (5+(1+q))) : List (Sparse.Poly (5+(1+q)) 1) :=
  typedGuard m generated address :: (SparseTransform.allWords n).flatMap (fun x =>
    typedRow m generated oneHot accepted address x ::
      if oneHot then List.ofFn (fun i : Fin cnt => typedSupport m generated oneHot accepted address i x) else [])

theorem supportAt_wire (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) :
    RuntimeTensorRows.supportAt (request m address) (List.ofFn x) =
      (List.ofFn (fun i : Fin cnt => typedSupport m generated oneHot accepted address i x)).map
        RationalInputMachine.rowWire := by
  change (List.range cnt).map _ = _
  rw [map_range_eq_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact support_wire m generated oneHot accepted address i x

theorem rows_wire (address : (Fin n → Bool) → Fin (5+(1+q))) :
    RuntimeTensorRows.rows oneHot (request m address)=
      RationalInputMachine.bodyWire (typedRows m generated oneHot accepted address) := by
  unfold RuntimeTensorRows.rows typedRows RationalInputMachine.bodyWire
  rw [guard_wire m generated address,List.map_cons]
  congr 1
  change ((RationalTableMachine.words n).flatMap _) = _
  rw [RationalTableMachine.words_eq,List.flatMap_map,List.map_flatMap]
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro x _
  rw [List.map_cons,row_wire m generated oneHot accepted address x]
  congr 1
  cases oneHot <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.map_nil]
  exact supportAt_wire m generated true accepted address x

theorem zeroRows_wire (address : (Fin n → Bool) → Fin (5+(1+q))) :
    RuntimeTensorRows.zeroRows (request m address)=
      RationalInputMachine.bodyWire ((SparseTransform.allWords n).map (entries address)) := by
  change (RationalTableMachine.words n).map _ = _
  simp only [RationalTableMachine.words_eq,List.map_map,RationalInputMachine.bodyWire,Function.comp_def,
    value_wire m address]

theorem compilerData : RationalCompiler.data=RationalCompiler.field.toArithmeticData := rfl

section Evaluation
variable {E : Type*} [Field E] (φ : ℚ →+* E) (z : Fin (5+(1+q)) → E)
local notation "ev" => SparseEvaluation.evaluate RationalCompiler.field φ z

/-- Evaluation uses the same inverse-matrix convention as the physical
transformed-entry machine, with original coefficients read at their bindings. -/
theorem entries_eval (address : (Fin n → Bool) → Fin (5+(1+q))) (g : Signature E n)
    (hbind : ∀y,z (address y)=g y) (x : Fin n → Bool) :
    ev (entries address x) =
      Signature.coordinateAction (fun _ => SymbolicTransform.inverse (SparseTransform.point z)) g x := by
  simp only [entries,compilerData,SymbolicInputTable.vertex_eval,
    SparseEvaluation.inverse_eval,SparseEvaluation.variable_eval,hbind]

theorem row_eval (address : (Fin n → Bool) → Fin (5+(1+q))) (x : Fin n → Bool) :
    ev (typedRow m generated oneHot accepted address x) =
      ev (entries address pvt) * TensorDecisionCleared.sliceProduct (fun y => ev (entries address y))
        cnt sz prt pvt x - ev (entries address x)*(ev (entries address pvt))^cnt := by
  simp only [typedRow,compilerData,SparseEvaluation.sub_eval,SparseEvaluation.mul_eval,SparseEvaluation.product_eval,
    List.map_ofFn,List.prod_ofFn,TensorDecisionCleared.sliceProduct]
  simp

theorem guard_eval (address : (Fin n → Bool) → Fin (5+(1+q))) :
    ev (typedGuard m generated address) =
      ev (entries address pvt)*z (Fin.natAdd 5 (0 : Fin (1+q)))-1 := by
  simp only [typedGuard,compilerData,SparseEvaluation.sub_eval,SparseEvaluation.mul_eval,SparseEvaluation.variable_eval,
    SparseEvaluation.one_eval]

theorem support_eval_zero_iff (address : (Fin n → Bool) → Fin (5+(1+q)))
    (i : Fin cnt) (x : Fin n → Bool) :
    ev (typedSupport m generated oneHot accepted address i x)=0 ↔
      1<Holant.weight (fun j => x (prt ⟨i,j⟩)) →
        ev (entries address (blockWord cnt sz prt pvt i (fun j => x (prt ⟨i,j⟩))))=0 := by
  unfold typedSupport
  by_cases h : RuntimeTensorRows.highWeight (Holant.weight (fun j => x (prt ⟨i,j⟩)))=true
  · rw [if_pos h]
    simp only [(RuntimeTensorRows.highWeight_correct _).mp h,true_implies]
  · rw [if_neg h]
    have hn : ¬1<Holant.weight (fun j => x (prt ⟨i,j⟩)) :=
      fun hlt => h ((RuntimeTensorRows.highWeight_correct _).mpr hlt)
    constructor
    · intro _ hlt
      exact (hn hlt).elim
    · intro _
      simp [SparseEvaluation.evaluate]

theorem support_constraints_iff (address : (Fin n → Bool) → Fin (5+(1+q))) :
    (∀x i,ev (typedSupport m generated oneHot accepted address i x)=0) ↔
      ∀i y,1<Holant.weight y → ev (entries address (blockWord cnt sz prt pvt i y))=0 := by
  simp only [support_eval_zero_iff]
  constructor
  · intro h i y hy
    let x := blockWord cnt sz prt pvt i y
    have hx : (fun j => x (prt ⟨i,j⟩))=y := by
      funext j
      exact blockWord_same _ _ _ _ _ _ _
    have h' := h x i
    rw [hx] at h'
    exact h' hy
  · intro h x i hx
    exact h i (fun j => x (prt ⟨i,j⟩)) hx

theorem rows_eval_iff (address : (Fin n → Bool) → Fin (5+(1+q))) :
    (∀p∈typedRows m generated oneHot accepted address,ev p=0) ↔
      ev (entries address pvt)*z (Fin.natAdd 5 (0 : Fin (1+q)))=1 ∧
      TensorDecisionCleared.Rows (fun y => ev (entries address y)) cnt sz prt pvt ∧
      (oneHot=true → ∀i y,1<Holant.weight y → ev (entries address (blockWord cnt sz prt pvt i y))=0) := by
  simp only [typedRows,List.forall_mem_cons,List.forall_mem_flatMap,SparseTransform.mem_allWords,
    forall_true_left,guard_eval,sub_eq_zero]
  have hrow : (∀x,ev (typedRow m generated oneHot accepted address x)=0) ↔
      TensorDecisionCleared.Rows (fun y => ev (entries address y)) cnt sz prt pvt := by
    simp only [row_eval,sub_eq_zero,TensorDecisionCleared.Rows]
  cases oneHot
  · simp only [Bool.false_eq_true,ite_false,List.not_mem_nil,false_implies,implies_true,
      and_true,hrow]
  · simp only [ite_true,List.forall_mem_ofFn_iff,forall_and,true_implies,hrow]
    rw [support_constraints_iff m generated true accepted φ z address]

theorem zeroRows_eval_iff (address : (Fin n → Bool) → Fin (5+(1+q))) :
    (∀p∈(SparseTransform.allWords n).map (entries address),ev p=0) ↔
      ∀x,ev (entries address x)=0 := by
  simp only [List.forall_mem_map,SparseTransform.mem_allWords,forall_true_left]

end Evaluation

end
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open TensorDecisionNormalization
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem flatten_ofFn_getD {A : Type} (d : A) {c : ℕ} (arity : Fin c → ℕ)
    (f : (i : Fin c) → Fin (arity i) → A) (i : Fin c) (j : Fin (arity i)) :
    (List.ofFn (fun k => List.ofFn (f k))).flatten.getD
      ((∑k : Fin i.val,arity (Fin.castLE i.isLt.le k))+j.val) d=f i j := by
  induction c with
  | zero => exact i.elim0
  | succ c ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.ofFn_succ,List.flatten_cons,Fin.val_zero,Fin.sum_univ_zero,zero_add]
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt)]
      exact PositiveCertificateMachine.getD_ofFn (f 0) j d
    | succ i =>
      rw [List.ofFn_succ,List.flatten_cons]
      have hs : (∑ k : Fin i.succ.val,arity (Fin.castLE i.succ.isLt.le k)) =
          arity 0+∑k : Fin i.val,arity (Fin.castLE i.isLt.le k).succ := by
        change (∑ k : Fin (i.val+1),arity (Fin.castLE i.succ.isLt.le k)) = _
        rw [Fin.sum_univ_succ]
        rfl
      rw [hs,List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
      rw [List.length_ofFn]
      have hn : arity 0+(∑k : Fin i.val,arity (Fin.castLE i.isLt.le k).succ)+j.val-arity 0 =
          (∑k : Fin i.val,arity (Fin.castLE i.isLt.le k).succ)+j.val := by omega
      rw [hn]
      exact ih (fun k => arity k.succ) (fun k => f k.succ) i j

theorem flatten_ofFn_eq {A : Type} (d : A) {c : ℕ} (arity : Fin c → ℕ)
    (f : (i : Fin c) → Fin (arity i) → A) :
    (List.ofFn (fun i => List.ofFn (f i))).flatten =
      List.ofFn (fun j : Fin (∑i,arity i) => f ((@finSigmaFinEquiv c arity).symm j).1 ((@finSigmaFinEquiv c arity).symm j).2) := by
  have hlen : (List.ofFn (fun i => List.ofFn (f i))).flatten.length=∑i,arity i := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen
  · intro j hj hj'
    let k : Fin (∑i,arity i) := ⟨j,by simpa only [List.length_ofFn] using hj'⟩
    have hp := (@finSigmaFinEquiv c arity).apply_symm_apply k
    have hv := congrArg Fin.val hp
    rw [finSigmaFinEquiv_apply] at hv
    rw [←List.getD_eq_getElem _ d hj,List.getElem_ofFn]
    change (List.ofFn (fun i => List.ofFn (f i))).flatten.getD k.val d =
      f ((@finSigmaFinEquiv c arity).symm k).1 ((@finSigmaFinEquiv c arity).symm k).2
    rw [←hv]
    exact flatten_ofFn_getD d arity f ((@finSigmaFinEquiv c arity).symm k).1 ((@finSigmaFinEquiv c arity).symm k).2

variable {n c : ℕ} (arity : Fin c → ℕ)
  (ports : (Σ i : Fin c,Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool)

theorem source_offset (i : Fin c) : RuntimeTensorRows.offset (List.ofFn arity,i.val)=
    ∑k : Fin i.val,arity (Fin.castLE i.isLt.le k) := by
  change (CommonFieldMachine.Coordinates.tab i.val (fun k => (List.ofFn arity).getD k 0)).sum = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  exact PositiveCertificateMachine.getD_ofFn arity (Fin.castLE i.isLt.le k) 0

theorem source_block (i : Fin c) : RuntimeTensorRows.block
    (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val) =
      List.ofFn (fun j : Fin (arity i) => (ports ⟨i,j⟩).val) := by
  unfold RuntimeTensorRows.block UniformTensorWitnessBranch.metadata
  simp only [PositiveCertificateMachine.getD_ofFn]
  change CommonFieldMachine.Coordinates.tab (arity i) _ = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [source_offset]
  have h : (List.finRange c).flatMap (fun k => (List.finRange (arity k)).map
      (fun l => (ports ⟨k,l⟩).val)) =
      (List.ofFn (fun k => List.ofFn (fun l => (ports ⟨k,l⟩).val))).flatten := by
    simp only [List.flatMap_def,←List.ofFn_eq_map]
  rw [h]
  exact flatten_ofFn_getD 0 arity (fun k l => (ports ⟨k,l⟩).val) i j

theorem source_block_mem (i a : Fin c) (b : Fin (arity a)) :
    (ports ⟨a,b⟩).val ∈ RuntimeTensorRows.block
      (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val) ↔ a=i := by
  rw [source_block arity ports pivot i,List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    exact (congrArg Sigma.fst (ports.injective (Fin.ext hj))).symm
  · rintro rfl
    exact ⟨b,rfl⟩

theorem source_sliceWord (i : Fin c) (x : Fin n → Bool) :
    RuntimeTensorRows.sliceWord (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val,List.ofFn x) =
      List.ofFn (blockWord c arity ports pivot i (fun j => x (ports ⟨i,j⟩))) := by
  unfold RuntimeTensorRows.sliceWord RuntimeTensorRows.slice
  change (List.range (List.ofFn pivot).length).map _ = _
  rw [List.length_ofFn]
  change CommonFieldMachine.Coordinates.tab n _ = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  apply congrArg List.ofFn
  funext j
  obtain ⟨⟨a,b⟩,rfl⟩ := ports.surjective j
  simp only [PositiveCertificateMachine.getD_ofFn]
  have ht : RuntimeTensorValidation.member (ports ⟨a,b⟩).val
      (RuntimeTensorRows.block (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val))=true ↔ a=i :=
    (RuntimeTensorValidation.member_correct _ _).trans (source_block_mem arity ports pivot i a b)
  by_cases h : a=i
  · subst a
    rw [ht.mpr rfl,if_pos rfl,blockWord_same]
  · have hf : RuntimeTensorValidation.member (ports ⟨a,b⟩).val
      (RuntimeTensorRows.block (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val))=false := by
      cases hh : RuntimeTensorValidation.member (ports ⟨a,b⟩).val
          (RuntimeTensorRows.block (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val))
      · rfl
      · exact (h (ht.mp hh)).elim
    rw [hf,if_neg Bool.false_ne_true,blockWord_other _ _ _ _ _ _ h]
    exact PositiveCertificateMachine.getD_ofFn pivot (ports ⟨a,b⟩) false

theorem source_block_weight (i : Fin c) (x : Fin n → Bool) :
    RuntimeTensorRows.weight (RuntimeTensorRows.block
      (UniformTensorWitnessBranch.metadata c arity ports pivot,i.val),List.ofFn x) =
      Holant.weight (fun j => x (ports ⟨i,j⟩)) := by
  simp only [RuntimeTensorRows.weight,source_block arity ports pivot i,
    List.map_ofFn,PositiveCertificateMachine.getD_ofFn,List.sum_ofFn,
    RuntimeTensorRows.bitNat,Holant.weight,Function.comp_def]

abbrev ShapeData (n : ℕ) := Σ c : ℕ, Σ arity : Fin c → ℕ,
  ((Σ i : Fin c,Fin (arity i)) ≃ Fin n) × (Fin n → Bool)

def encodeShape (s : ShapeData n) : UniformTensorWitnessBranch.Metadata :=
  UniformTensorWitnessBranch.metadata s.1 s.2.1 s.2.2.1 s.2.2.2

theorem encodeShape_injective : Function.Injective (encodeShape (n:=n)) := by
  rintro ⟨c,a,e,p⟩ ⟨c',a',e',p'⟩ h
  have hc := congrArg (fun m : UniformTensorWitnessBranch.Metadata => m.1.length) h
  simp only [encodeShape,UniformTensorWitnessBranch.metadata,List.length_ofFn] at hc
  subst c'
  have ha : a=a' := List.ofFn_injective (congrArg Prod.fst h)
  subst a'
  have hp : p=p' := List.ofFn_injective (congrArg (fun m : UniformTensorWitnessBranch.Metadata => m.2.2) h)
  subst p'
  have he : e=e' := by
    apply Equiv.ext
    rintro ⟨i,j⟩
    have hb : List.ofFn (fun k : Fin (a i) => (e ⟨i,k⟩).val) =
        List.ofFn (fun k : Fin (a i) => (e' ⟨i,k⟩).val) := by
      rw [←source_block a e p i,←source_block a e' p i]
      change RuntimeTensorRows.block (encodeShape ⟨c,a,e,p⟩,i.val) =
        RuntimeTensorRows.block (encodeShape ⟨c,a,e',p⟩,i.val)
      rw [h]
    exact Fin.ext (congrFun (List.ofFn_injective hb) j)
  subst e'
  rfl

section Reification
variable (m : UniformTensorWitnessBranch.Metadata) (generated : m ∈ RuntimeTensorCatalogue.catalogue n)
  (oneHot : Bool) (accepted : RuntimeTensorValidation.valid (oneHot,n,m)=true)
local notation "cnt" => RuntimeTensorReification.count m
local notation "sz" => RuntimeTensorReification.arity m
local notation "prt" => RuntimeTensorReification.blockPorts m generated oneHot accepted
local notation "pvt" => RuntimeTensorReification.pivot m generated

def reifiedShape : ShapeData n := ⟨cnt,sz,prt,pvt⟩

theorem encode_reifiedShape : encodeShape (reifiedShape m generated oneHot accepted)=m := by
  apply Prod.ext
  · exact List.ofFn_get m.1
  · apply Prod.ext
    · change (List.finRange cnt).flatMap
        (fun i => (List.finRange (sz i)).map (fun j => (prt ⟨i,j⟩).val)) = m.2.1
      simp only [List.flatMap_def,←List.ofFn_eq_map]
      rw [flatten_ofFn_eq 0 sz]
      apply List.ext_getElem
      · simpa only [List.length_ofFn,RuntimeTensorReification.size_sum m oneHot accepted] using
          (RuntimeTensorCatalogue.generated_bounds n m generated).2.2.1.symm
      · intro j hj hj'
        simp only [List.getElem_ofFn]
        rw [RuntimeTensorReification.blockPorts_raw m generated oneHot accepted]
        simp only [Sigma.eta,Equiv.apply_symm_apply]
        rfl
    · change List.ofFn pvt=m.2.2
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using (RuntimeTensorCatalogue.generated_bounds n m generated).2.2.2.2.symm
      · intro j hj hj'
        simp only [List.getElem_ofFn]
        rfl
end Reification

theorem source_shape_roundtrip (s : ShapeData n)
    (generated : encodeShape s ∈ RuntimeTensorCatalogue.catalogue n) (oneHot : Bool)
    (accepted : RuntimeTensorValidation.valid (oneHot,n,encodeShape s)=true) :
    reifiedShape (encodeShape s) generated oneHot accepted=s := by
  apply encodeShape_injective
  exact encode_reifiedShape _ generated oneHot accepted

section CandidateSemantics
variable {K : Type*} [Field K]

def shapeBranchTest (oneHot : Bool) (f : Signature K n) (s : ShapeData n) : Prop :=
  UniformTensorDecisionSyntax.BranchTest oneHot f s.1 s.2.1 s.2.2.1 s.2.2.2

/-- This is the semantic interpretation of the actual generated and accepted
candidate list. Its proof witnesses are erased and never machine inputs. -/
def RawNonzeroTest (oneHot : Bool) (f : Signature K n) : Prop :=
  ∃m,∃generated : m ∈ RuntimeTensorCatalogue.catalogue n,
    ∃accepted : RuntimeTensorValidation.valid (oneHot,n,m)=true,
      shapeBranchTest oneHot f (reifiedShape m generated oneHot accepted)

def RawFiniteTest (oneHot : Bool) (f : Signature K n) : Prop :=
  (∀x,f x=0) ∨ RawNonzeroTest oneHot f

theorem arity_candidates_iff (f : Signature K n) :
    RawNonzeroTest false f ↔ ∃S : TensorDecision.Shape n,∃p,TensorDecisionCleared.ArityTwoAccepts f S p := by
  constructor
  · rintro ⟨m,generated,accepted,h⟩
    let S := RuntimeTensorReification.arityShape m generated accepted
    refine ⟨S,RuntimeTensorReification.pivot m generated,?_⟩
    exact (UniformTensorDecisionSyntax.arityTwo_branch_iff f S _).mp h
  · rintro ⟨S,p,h⟩
    let s : ShapeData n := ⟨S.count,S.arity,S.ports,p⟩
    have generated : encodeShape s ∈ RuntimeTensorCatalogue.catalogue n :=
      RuntimeTensorCatalogue.arity_shape_mem S p
    have accepted : RuntimeTensorValidation.valid (false,n,encodeShape s)=true :=
      RuntimeTensorValidation.arity_shape_valid S p
    refine ⟨encodeShape s,generated,accepted,?_⟩
    rw [source_shape_roundtrip s generated false accepted]
    exact (UniformTensorDecisionSyntax.arityTwo_branch_iff f S p).mpr h

theorem matching_candidates_iff (f : Signature K n) :
    RawNonzeroTest true f ↔ ∃S : TensorDecisionStable.Shape n,∃p,TensorDecisionCleared.OneHotAccepts f S p := by
  constructor
  · rintro ⟨m,generated,accepted,h⟩
    let S := RuntimeTensorReification.matchingShape m generated accepted
    refine ⟨S,RuntimeTensorReification.pivot m generated,?_⟩
    exact (UniformTensorDecisionSyntax.oneHot_branch_iff f S _).mp h
  · rintro ⟨S,p,h⟩
    let s : ShapeData n := ⟨S.count,S.arity,S.ports,p⟩
    have generated : encodeShape s ∈ RuntimeTensorCatalogue.catalogue n :=
      RuntimeTensorCatalogue.matching_shape_mem S p
    have accepted : RuntimeTensorValidation.valid (true,n,encodeShape s)=true :=
      RuntimeTensorValidation.matching_shape_valid S p
    refine ⟨encodeShape s,generated,accepted,?_⟩
    rw [source_shape_roundtrip s generated true accepted]
    exact (UniformTensorDecisionSyntax.oneHot_branch_iff f S p).mpr h

theorem arity_finiteTest_iff (f : Signature K n) :
    RawFiniteTest false f ↔ TensorDecisionCleared.ArityTwoTest f := by
  simp only [RawFiniteTest,arity_candidates_iff,TensorDecisionCleared.ArityTwoTest]

theorem matching_finiteTest_iff (f : Signature K n) :
    RawFiniteTest true f ↔ TensorDecisionCleared.OneHotTest f := by
  simp only [RawFiniteTest,matching_candidates_iff,TensorDecisionCleared.OneHotTest]

/-- Exact ordinary source predicate for the generated catalogue specification;
the promised RootCode search loop is a separate programme composition. -/
theorem arity_source_iff (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (fun m _ => m=1 ∨ m=2) f ↔ RawFiniteTest false f :=
  (TensorDecisionCleared.arityTwo_source_iff f).trans (arity_finiteTest_iff f).symm

/-- The same generated catalogue suffices for either fixed family-wide K/KX
orientation. Selecting and retaining that shared orientation is external to
this one-signature row component. -/
theorem matching_source_iff (opposite : Bool) (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (matchingImage opposite) f ↔
      RawFiniteTest true ((TensorDecisionMatching.basis opposite).symm.action f) :=
  (TensorDecisionCleared.matching_source_iff opposite f).trans (matching_finiteTest_iff _).symm

end CandidateSemantics

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRowsSoundness
