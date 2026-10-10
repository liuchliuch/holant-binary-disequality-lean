import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockValidity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSemantics
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingSource

/-! The exact even-CSP records for one actual unary block. Two existing pins
fix each reserved constant, and all private variables keep their own slots. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRaw
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (ports guards coefficient)
export OrdinaryNegativeSparseMixingSource (Block)
end D
namespace V
export OrdinaryNegativeMixedBlockValidity (even_map)
export OrdinaryNegativePhaseBundleValidity (guards_good guards_even)
end V
namespace S
export OrdinaryNegativeMixedBlockSemantics (mapped_weight guards_weight weight_append)
end S
namespace W
export StableHigherCurrentOrdinarySquare (degree_flat weight extend rowValue)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (row : D.Block (s:=s) (b:=a) 1)

def address : Bool ⊕ Fin (1+row.privateCount)→ℕ := Sum.elim (fun b=>if b then 1 else 0) (fun i=>i.val+2)

def factors : List (Fin s×List ℕ) :=
  (row.rows 0).map (fun node=>(node.1,List.ofFn (fun i=>address row (node.2 i))))

variable (p0 p1 : Fin s)
def raw : Raw := ⟨(1+row.privateCount)+2,(factors row).map OrdinaryNegativeMixedBlockData.factor++D.guards p0 p1⟩

theorem factors_addresses : (factors row).flatMap Prod.snd=(D.ports row.rows 0).map (address row) := by
  simp only [factors,D.ports,List.flatMap_map,Function.comp_def,List.map_flatMap,List.map_ofFn]

theorem raw_even (i : ℕ) : Even ((raw row p0 p1).degree i) := by
  rw [W.degree_flat]
  simp only [raw,List.flatMap_append,List.count_append,List.flatMap_map,OrdinaryNegativeMixedBlockData.factor]
  apply Even.add _ (V.guards_even p0 p1 i)
  rw [factors_addresses]
  exact V.even_map (D.ports row.rows 0) (row.balanced 0) (address row) i

variable (h0 : a p0.val=1) (h1 : a p1.val=1)
include h0 h1 in
theorem good : ∀factor∈(raw row p0 p1).factors,
    factor.1<s ∧ factor.2.length=a factor.1 ∧ ∀i∈factor.2,i<(1+row.privateCount)+2 := by
  intro factor hf
  rcases List.mem_append.mp hf with hf|hf
  · obtain ⟨typed,ht,rfl⟩ := List.mem_map.mp hf
    obtain ⟨node,_,rfl⟩ := List.mem_map.mp ht
    refine ⟨node.1.isLt,by simp only [OrdinaryNegativeMixedBlockData.factor,List.length_ofFn];rfl,?_⟩
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    cases hp : node.2 j with
    | inl bit=>cases bit <;> simp [address]
    | inr q=>
        change q.val+2<(1+row.privateCount)+2
        have hq : q.val<1+row.privateCount := q.isLt
        omega
  · exact V.guards_good p0 p1 h0 h1 (1+row.privateCount) factor hf

include h0 h1 in
theorem valid : (raw row p0 p1).Valid s a := by
  have hg:=good row p0 p1 h0 h1
  refine ⟨?_,?_,fun i _=>raw_even row p0 p1 i⟩
  · intro v
    have h:=hg _ (List.get_mem _ v)
    exact ⟨h.1,h.2.1⟩
  · intro p
    exact (hg _ (List.get_mem _ p.1)).2.2 _ (List.get_mem _ p.2)

def input : Raw.Input s a := ⟨raw row p0 p1,valid row p0 p1 h0 h1⟩

def marker : Fin (input row p0 p1 h0 h1).val.variables := ⟨2,by change 2<(1+row.privateCount)+2;omega⟩

variable (H : (i : Fin s)→Signature K (a i.val))
variable (h0lit : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1lit : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

include h0lit h1lit in
theorem raw_weight (x : ℕ→Bool) : W.weight H (raw row p0 p1).factors x=
    (if x 0=false ∧ x 1=true then 1 else 0)*
      (((row.rows 0).map (fun node=>H node.1 (fun i=>x (address row (node.2 i))))).prod) := by
  rw [raw,S.weight_append,S.guards_weight H p0 p1 h0lit h1lit,S.mapped_weight]
  simp only [factors,List.map_map,Function.comp_def]
  rw [mul_comm]
  congr 1
  congr 1
  apply List.map_congr_left
  intro node _
  congr 1
  funext i
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn];exact i.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRaw
end
