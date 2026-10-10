import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonalRaw
import Holant.Proofs.Counting.CircuitSemantics

/-! The root-conditioned partition of the literal unary-block records is
exactly that block's value. Reserved pins and every private sum are eliminated
once, with no omitted variables or scalar correction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRawValue
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (coefficient)
export OrdinaryNegativeSparseMixingSource (Block)
end D
namespace R
export NoXGeneralEvenDiagonalRaw (address raw input marker raw_weight)
end R
namespace W
export StableHigherCurrentOrdinarySquare (weight extend rowValue)
end W
namespace Pn
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinRaw (sum_cons)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

theorem typed_weight (r : Raw.Input s a) (x : Fin r.val.variables→Bool) :
    Raw.factorWeight H r (fun p=>x (Raw.route r p))=W.weight H r.val.factors (W.extend x) := by
  change (∏v : Fin r.val.factors.length,H (Raw.label r v)
    (fun j=>x (Raw.route r (Raw.portCast r v j))))=_
  calc
    _=∏v : Fin r.val.factors.length,W.rowValue H (r.val.factors.get v) (W.extend x) := by
      apply Finset.prod_congr rfl
      intro v _
      unfold W.rowValue
      rw [dite_eq_left (r.property.1 v).1]
      congr 1
      funext j
      have hl : j.val<(r.val.factors.get v).2.length := by rw [(r.property.1 v).2];exact j.isLt
      rw [List.getD_eq_getElem _ _ hl]
      have hp:=r.property.2.1 (Raw.portCast r v j)
      simp only [Raw.address,Raw.portCast,Fin.val_cast,List.get_eq_getElem] at hp
      simp only [W.extend,dite_eq_left hp,Raw.route,Raw.address,Raw.portCast,List.get_eq_getElem,Fin.val_cast]
    _=_ := by
      rw [←List.prod_ofFn]
      apply congrArg List.prod
      simpa only [W.weight,List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map r.val.factors (fun row=>W.rowValue H row (W.extend x)))

variable (row : D.Block (s:=s) (b:=a) 1) (p0 p1 : Fin s)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

theorem address_read (x : Fin (1+row.privateCount)→Bool) (p : Bool ⊕ Fin (1+row.privateCount)) :
    W.extend (Fin.cons false (Fin.cons true x)) (R.address row p)=Sum.elim id x p := by
  cases p with
  | inl bit=>cases bit <;> simp [R.address,W.extend]
  | inr i=>
      change (if h : i.val+2<(1+row.privateCount)+2 then
        (Fin.cons false (Fin.cons true x) : Fin ((1+row.privateCount)+2)→Bool) ⟨i.val+2,h⟩ else false)=x i
      rw [dite_eq_left (by omega)]
      change (Fin.cons false (Fin.cons true x) : Fin ((1+row.privateCount)+2)→Bool) i.succ.succ=x i
      rfl

include h0 h1 in
theorem weight_cons (q r : Bool) (x : Fin (1+row.privateCount)→Bool) :
    W.weight H (R.raw row p0 p1).factors (W.extend (Fin.cons q (Fin.cons r x)))=
      if q=false ∧ r=true then D.coefficient H row.rows 0 x else 0 := by
  rw [R.raw_weight row p0 p1 H h0 h1]
  have e0 : W.extend (Fin.cons q (Fin.cons r x)) 0=q := by simp [W.extend]
  have e1 : W.extend (Fin.cons q (Fin.cons r x)) 1=r := by simp [W.extend]
  rw [e0,e1]
  by_cases h : q=false ∧ r=true
  · rw [ite_eq_left h,one_mul,ite_eq_left h]
    rcases h with ⟨rfl,rfl⟩
    change _=((row.rows 0).map (fun node=>H node.1 (fun i=>Sum.elim id x (node.2 i)))).prod
    simp_rw [address_read]
  · rw [ite_eq_right h,zero_mul,ite_eq_right h]

def sourceInput := R.input row p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1)
def sourceVariable := R.marker row p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1)

include h0 h1 in
theorem conditional (b : Bool) :
    (∑x : Fin (sourceInput H row p0 p1 h0 h1).val.variables→Bool,
      if x (sourceVariable H row p0 p1 h0 h1)=b then
        Raw.factorWeight H (sourceInput H row p0 p1 h0 h1)
          (fun p=>x (Raw.route (sourceInput H row p0 p1 h0 h1) p)) else 0)=
      row.signature H (fun _=>b) := by
  classical
  simp_rw [typed_weight]
  change (∑x : Fin ((1+row.privateCount)+2)→Bool,
    if x ⟨2,by omega⟩=b then W.weight H (R.raw row p0 p1).factors (W.extend x) else 0)=_
  rw [Pn.sum_cons]
  simp_rw [Pn.sum_cons,weight_cons H row p0 p1 h0 h1]
  simp only [Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,
    and_false,and_true,ite_false,ite_true,ite_self,Finset.sum_const_zero,add_zero,zero_add]
  rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_block 1 row.privateCount]
  rw [←Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm]
  change (∑q : Bool,∑y : Fin row.privateCount→Bool,
    if q=b then D.coefficient H row.rows 0 (Fin.addCases (fun _=>q) y) else 0)=_
  cases b <;> simp only [Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,
    ite_true,ite_false,Finset.sum_const_zero,zero_add,add_zero] <;> rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRawValue
end
