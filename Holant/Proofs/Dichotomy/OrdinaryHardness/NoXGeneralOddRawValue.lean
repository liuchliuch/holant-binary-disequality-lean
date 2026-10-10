import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTable
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonalRawValue

/-! Conditioning the marked boundary slots in the auxiliary closed records
recovers the complete odd resource, including every original private sum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRawValue
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace R
export NoXGeneralOddRaw (arity factors markedFactors address raw input)
end R
namespace T
export NoXGeneralOddTable (table old old_literal)
end T
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
export OrdinaryNegativeMixedBlockData (guards coefficient)
end D
namespace W
export StableHigherCurrentOrdinarySquare (weight rowValue extend)
end W
namespace S
export OrdinaryNegativeMixedBlockSemantics (literal_row weight_append guards_weight)
end S
namespace Pn
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinRaw (sum_cons)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (row : D.OddResource (s:=s) a n)
variable (p0 p1 : Fin s)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

theorem marked_weight (x : ℕ→Bool) : W.weight (T.table H) (R.markedFactors row) x=1 := by
  simp [W.weight,R.markedFactors,List.map_ofFn,List.prod_ofFn,W.rowValue,T.table]

theorem factors_weight (x : ℕ→Bool) : W.weight (T.table H) (R.factors row) x=
    ((row.rows 0).map (fun node=>H node.1 (fun i=>x (R.address row (node.2 i))))).prod := by
  simp only [W.weight,R.factors,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro node _
  have value:=S.literal_row (T.table H) (T.old node.1) (H node.1) (T.old_literal H node.1)
    (List.ofFn (fun i=>R.address row (node.2 i))) x
  change W.rowValue (T.table H) ((T.old node.1).val,_) x=_
  rw [value]
  congr 1
  funext i
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn];exact i.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]

include h0 h1 in
theorem raw_weight (x : ℕ→Bool) : W.weight (T.table H) (R.raw row p0 p1).factors x=
    (if x 0=false ∧ x 1=true then 1 else 0)*
      (((row.rows 0).map (fun node=>H node.1 (fun i=>x (R.address row (node.2 i))))).prod) := by
  rw [R.raw,S.weight_append,S.weight_append,marked_weight,factors_weight,one_mul]
  have guards : W.weight (T.table H) (D.guards p0 p1) x=if x 0=false ∧ x 1=true then 1 else 0 :=
    S.guards_weight (T.table H) (T.old p0) (T.old p1)
      ((T.old_literal H p0).trans h0) ((T.old_literal H p1).trans h1) x
  rw [guards,mul_comm]

theorem address_read (x : Fin (n+row.privateCount)→Bool) (p : Bool ⊕ Fin (n+row.privateCount)) :
    W.extend (Fin.cons false (Fin.cons true x)) (R.address row p)=Sum.elim id x p := by
  cases p with
  | inl bit=>cases bit <;> simp [R.address,W.extend]
  | inr i=>
      change (if h : i.val+2<(n+row.privateCount)+2 then
        (Fin.cons false (Fin.cons true x) : Fin ((n+row.privateCount)+2)→Bool) ⟨i.val+2,h⟩ else false)=x i
      rw [dite_eq_left (by omega)]
      change (Fin.cons false (Fin.cons true x) : Fin ((n+row.privateCount)+2)→Bool) i.succ.succ=x i
      rfl

include h0 h1 in
theorem weight_cons (q r : Bool) (x : Fin (n+row.privateCount)→Bool) :
    W.weight (T.table H) (R.raw row p0 p1).factors (W.extend (Fin.cons q (Fin.cons r x)))=
      if q=false ∧ r=true then D.coefficient H row.rows 0 x else 0 := by
  rw [raw_weight H row p0 p1 h0 h1]
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
def sourceVariable (j : Fin n) : Fin (sourceInput H row p0 p1 h0 h1).val.variables :=
  ⟨j.val+2,by change j.val+2<(n+row.privateCount)+2;omega⟩

include h0 h1 in
theorem conditional (z : Fin n→Bool) :
    (∑x : Fin (sourceInput H row p0 p1 h0 h1).val.variables→Bool,
      if (fun j=>x (sourceVariable H row p0 p1 h0 h1 j))=z then
        Raw.factorWeight (T.table H) (sourceInput H row p0 p1 h0 h1)
          (fun p=>x (Raw.route (sourceInput H row p0 p1 h0 h1) p)) else 0)=
      row.signature H z := by
  classical
  simp_rw [NoXGeneralEvenDiagonalRawValue.typed_weight]
  change (∑x : Fin ((n+row.privateCount)+2)→Bool,
    if (fun j : Fin n=>x ⟨j.val+2,by omega⟩)=z then
      W.weight (T.table H) (R.raw row p0 p1).factors (W.extend x) else 0)=_
  rw [Pn.sum_cons]
  simp_rw [Pn.sum_cons,weight_cons H row p0 p1 h0 h1]
  simp only [Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,and_false,and_true,
    ite_false,ite_true,ite_self,Finset.sum_const_zero,add_zero,zero_add]
  rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_block n row.privateCount]
  have front (q : Fin n→Bool) (y : Fin row.privateCount→Bool) :
      (fun j : Fin n=>(Fin.cons false (Fin.cons true (Fin.addCases q y)) : Fin ((n+row.privateCount)+2)→Bool)
        ⟨j.val+2,by omega⟩)=q := by
    funext j
    change (Fin.cons false (Fin.cons true (Fin.addCases q y)) : Fin ((n+row.privateCount)+2)→Bool)
      (Fin.castAdd row.privateCount j).succ.succ=q j
    simp only [Fin.cons_succ,Fin.addCases_left]
  simp_rw [front]
  change (∑q : Fin n→Bool,∑y : Fin row.privateCount→Bool,
    if q=z then D.coefficient H row.rows 0 (Fin.addCases q y) else 0)=_
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddRawValue
end
