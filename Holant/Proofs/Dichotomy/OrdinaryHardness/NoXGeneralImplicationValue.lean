import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralImplicationQuery
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeBinaryThreeUnsignedStarGraph

/-! Exact partition semantics for the literal signed-NAND to signed-implication
writer. Every fresh vertex is summed once, giving the proved NAND identity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationValue
open Holant Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.CountingBridge
open scoped BigOperators
namespace Q
export NoXGeneralImplicationQuery (expand edgeRows fresh selected_mem)
end Q
namespace N
export BinaryThreeSupportGraph (Raw rowsWeight value extend extend_apply)
end N
namespace I
export OrdinaryNegativeBinaryThreeUnsignedStarGraph.R (rowsWeight value)
end I
namespace G
export BinaryThreeSupportGates (nand sign implication implication_nand)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K]

def assignments (r : N.Raw) : (Fin (Q.expand r).variables→Bool) ≃
    ((Fin r.variables→Bool)×(Fin r.edges.length→Bool)) :=
  CircuitSemantics.blockEquiv r.variables r.edges.length

theorem old_assignment (r : N.Raw) (z : Fin (Q.expand r).variables→Bool)
    (v : ℕ) (hv : v<r.variables) : N.extend z v=N.extend (assignments r z).1 v := by
  have h : v<(Q.expand r).variables := hv.trans_le (Nat.le_add_right _ _)
  rw [N.extend,N.extend,dite_eq_left h,dite_eq_left hv]
  rfl

theorem fresh_assignment (r : N.Raw) (z : Fin (Q.expand r).variables→Bool) (i : Fin r.edges.length) :
    N.extend z (r.variables+i.val)=(assignments r z).2 i := by
  have h : r.variables+i.val<(Q.expand r).variables := Nat.add_lt_add_left i.isLt _
  rw [N.extend,dite_eq_left h]
  rfl

private theorem map_range_product (n : ℕ) (f : ℕ→K) :
    ((List.range n).map f).prod=∏i : Fin n,f i.val := by
  induction n with
  | zero=>simp
  | succ n ih=>simp [List.prod_range_succ,Fin.prod_univ_castSucc,ih]

private theorem prod_flatMap {A : Type} (l : List A) (f : A→List K) :
    (l.flatMap f).prod=(l.map (fun i=>(f i).prod)).prod := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp [ih]

def oldSigns (r : N.Raw) (x : Fin r.variables→Bool) : K :=
  (r.signs.map (fun i=>G.sign (N.extend x i))).prod

def factor (r : N.Raw) (x : Fin r.variables→Bool) (i : Fin r.edges.length) (z : Bool) : K :=
  G.sign z*G.implication z (N.extend x (r.edges.get i).1)*G.implication z (N.extend x (r.edges.get i).2)

theorem edge_product (r : N.Raw) (hr : r.WellFormed) (z : Fin (Q.expand r).variables→Bool) :
    ((Q.expand r).edges.map (fun e=>G.implication (K:=K) (N.extend z e.1) (N.extend z e.2))).prod=
      ∏i : Fin r.edges.length,
        G.implication ((assignments r z).2 i) (N.extend (assignments r z).1 (r.edges.get i).1)*
        G.implication ((assignments r z).2 i) (N.extend (assignments r z).1 (r.edges.get i).2) := by
  change (((List.range r.edges.length).flatMap (Q.edgeRows r)).map _).prod=_
  simp only [List.map_flatMap,prod_flatMap,map_range_product]
  apply Finset.prod_congr rfl
  intro i _
  have bounds:=hr.1 _ (List.get_mem r.edges i)
  simp only [Q.edgeRows,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    List.getD_eq_get r.edges (0,0) i,fresh_assignment,
    old_assignment r z _ bounds.1,old_assignment r z _ bounds.2]

theorem weight (r : N.Raw) (hr : r.WellFormed) (z : Fin (Q.expand r).variables→Bool) :
    I.rowsWeight (K:=K) ((Q.expand r).edges,(Q.expand r).signs) (N.extend z)=
      oldSigns r (assignments r z).1 * ∏i,factor r (assignments r z).1 i ((assignments r z).2 i) := by
  have old : (r.signs.map (fun v=>G.sign (K:=K) (N.extend z v))).prod=oldSigns r (assignments r z).1 := by
    unfold oldSigns
    congr 1
    apply List.map_congr_left
    intro v hv
    rw [old_assignment r z v (hr.2 v hv)]
  have fresh : ((Q.fresh r).map (fun v=>G.sign (K:=K) (N.extend z v))).prod=
      ∏i : Fin r.edges.length,G.sign ((assignments r z).2 i) := by
    simp only [Q.fresh,List.map_map,map_range_product,Function.comp_def,fresh_assignment]
  unfold I.rowsWeight
  rw [edge_product r hr z]
  change _*( (r.signs++Q.fresh r).map _).prod=_
  rw [List.map_append,List.prod_append,old,fresh]
  simp only [factor,Finset.prod_mul_distrib]
  ring

theorem nand_product (r : N.Raw) (x : Fin r.variables→Bool) :
    (r.edges.map (fun e=>G.nand (K:=K) (N.extend x e.1) (N.extend x e.2))).prod=
      ∏i : Fin r.edges.length,G.nand (N.extend x (r.edges.get i).1) (N.extend x (r.edges.get i).2) := by
  conv_lhs=>rw [←List.ofFn_get r.edges]
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def]

theorem value (r : N.Raw) (hr : r.WellFormed) : I.value (K:=K) (Q.expand r)=N.value (K:=K) r := by
  unfold I.value
  rw [←(assignments r).symm.sum_comp]
  simp only [Fintype.sum_prod_type,weight r hr,Equiv.apply_symm_apply]
  unfold N.value N.rowsWeight
  apply Finset.sum_congr rfl
  intro x _
  rw [←Finset.mul_sum,←Fintype.prod_sum]
  have factorEq (i : Fin r.edges.length) : (∑z : Bool,factor (K:=K) r x i z)=
      G.nand (N.extend x (r.edges.get i).1) (N.extend x (r.edges.get i).2) :=
    G.implication_nand _ _
  simp_rw [factorEq]
  rw [←nand_product]
  exact mul_comm _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralImplicationValue
end
