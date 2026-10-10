import Holant.Proofs.Hardness.BinaryThreeSupportGraph
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeBinaryThreeUnsignedStars
import Holant.Proofs.Hardness.BinaryCSPProgrammeStars

/-! Exact semantics of the physical star writer's literal raw graph. Old
variables, repeated sign addresses, isolated variables, loops and empty lists
are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryThreeUnsignedStarGraph
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant
open Holant.LocalDrafts.RemoteWork.CountingBridge
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype
namespace R
export BinaryThreeSupportGraph (Raw extend extend_apply)
def rowsWeight {K : Type*} [CommRing K] (r : List (ℕ×ℕ)×List ℕ) (ρ : ℕ→Bool) : K :=
  (r.1.map (fun e=>BinaryThreeSupportGates.implication (ρ e.1) (ρ e.2))).prod *
    (r.2.map (fun v=>BinaryThreeSupportGates.sign (ρ v))).prod
def value {K : Type*} [CommRing K] (r : Raw) : K :=
  ∑x : Fin r.variables→Bool,rowsWeight (r.edges,r.signs) (extend x)
end R
namespace W
export BinaryCSPProgrammeStars (leafEdges expand)
end W
namespace S
export OrdinaryNegativeBinaryThreeUnsignedStars (sample signed signed_interpolation)
end S
namespace G
export BinaryThreeSupportGates (implication sign)
end G

def leavesEquiv (m k : ℕ) : (Fin (m*k)→Bool) ≃ (Fin m→Fin k→Bool) where
  toFun z i j := z (finProdFinEquiv (i,j))
  invFun z v := z (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2
  left_inv := by
    intro z
    funext v
    change z (finProdFinEquiv (finProdFinEquiv.symm v))=z v
    rw [Equiv.apply_symm_apply]
  right_inv := by intro z; funext i j; simp

def assignments (r : R.Raw) (k : ℕ) :
    (Fin (W.expand r k).variables→Bool) ≃
      ((Fin r.variables→Bool) × (Fin r.signs.length→Fin k→Bool)) :=
  (CircuitSemantics.blockEquiv r.variables (r.signs.length*k)).trans
    (Equiv.prodCongr (Equiv.refl _) (leavesEquiv r.signs.length k))

variable {K : Type*} [Field K]

def base (r : R.Raw) (x : Fin r.variables→Bool) : K :=
  (r.edges.map (fun e=>G.implication (R.extend x e.1) (R.extend x e.2))).prod

def bits (r : R.Raw) (x : Fin r.variables→Bool) (i : Fin r.signs.length) : Bool :=
  R.extend x (r.signs.get i)

theorem signed_eq (r : R.Raw) : R.value (K:=K) r=S.signed (base r) (bits r) := by
  unfold R.value S.signed
  apply Finset.sum_congr rfl
  intro x _
  unfold R.rowsWeight base
  congr 1
  have h := List.ofFn_get r.signs
  calc
    (r.signs.map (fun v=>G.sign (K:=K) (R.extend x v))).prod=
      ((List.ofFn (fun i : Fin r.signs.length=>r.signs.get i)).map
        (fun v=>G.sign (K:=K) (R.extend x v))).prod := by rw [h]
    _=∏i : Fin r.signs.length,G.sign (K:=K) (bits r x i) := by
      rw [List.map_ofFn,List.prod_ofFn]
      rfl

theorem old_assignment (r : R.Raw) (k : ℕ)
    (z : Fin (W.expand r k).variables→Bool) (v : ℕ) (hv : v<r.variables) :
    R.extend z v=R.extend (assignments r k z).1 v := by
  have h : v<(W.expand r k).variables := hv.trans_le (Nat.le_add_right _ _)
  rw [R.extend,R.extend,dite_eq_left h,dite_eq_left hv]
  rfl

theorem leaf_assignment (r : R.Raw) (k : ℕ)
    (z : Fin (W.expand r k).variables→Bool) (i : Fin r.signs.length) (j : Fin k) :
    R.extend z (r.variables+i.val*k+j.val)=(assignments r k z).2 i j := by
  have h : r.variables+i.val*k+j.val<(W.expand r k).variables := by
    have hm := Nat.mul_le_mul_right k i.isLt
    simp only [W.expand]
    nlinarith [j.isLt]
  rw [R.extend,dite_eq_left h]
  change z ⟨r.variables+i.val*k+j.val,h⟩=
    z (Fin.natAdd r.variables (finProdFinEquiv (i,j)))
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv,Nat.mul_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem map_range_product (n : ℕ) (f : ℕ→K) :
    ((List.range n).map f).prod=∏i : Fin n,f i.val := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.prod_range_succ,Fin.prod_univ_castSucc,ih]

private theorem prod_flatMap {A : Type*} (l : List A) (f : A→List K) :
    (l.flatMap f).prod=(l.map (fun i=>(f i).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem leaf_product (r : R.Raw) (hr : r.WellFormed) (k : ℕ)
    (z : Fin (W.expand r k).variables→Bool) :
    ((W.leafEdges r k).map (fun e=>G.implication (K:=K) (R.extend z e.1) (R.extend z e.2))).prod=
      ∏i : Fin r.signs.length,∏j : Fin k,
        G.implication (bits r (assignments r k z).1 i) ((assignments r k z).2 i j) := by
  unfold W.leafEdges
  simp only [List.map_flatMap,List.map_map,prod_flatMap,map_range_product]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Function.comp_def]
  rw [List.getD_eq_get r.signs 0 i,
    old_assignment r k z _ (hr.2 _ (List.get_mem _ _)),leaf_assignment r k z i j]
  rfl

theorem expansion_row (r : R.Raw) (hr : r.WellFormed) (k : ℕ)
    (z : Fin (W.expand r k).variables→Bool) :
    R.rowsWeight (K:=K) ((W.expand r k).edges,(W.expand r k).signs) (R.extend z)=
      base r (assignments r k z).1 *
        ∏i : Fin r.signs.length,∏j : Fin k,
          G.implication (bits r (assignments r k z).1 i) ((assignments r k z).2 i j) := by
  simp only [R.rowsWeight,W.expand,List.map_append,List.prod_append,List.map_nil,List.prod_nil,mul_one]
  rw [leaf_product r hr k z]
  congr 1
  unfold base
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  rw [old_assignment r k z _ (hr.1 e he).1,old_assignment r k z _ (hr.1 e he).2]
  rfl

theorem expand_value (r : R.Raw) (hr : r.WellFormed) (k : ℕ) :
    R.value (K:=K) (W.expand r k)=S.sample (base r) (bits r) k := by
  unfold R.value S.sample
  simp_rw [expansion_row r hr k]
  rw [←(assignments r k).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]

variable [CharZero K]

/-- Only literal unsigned graphs emitted by the proved physical star writer
are queried in this finite formula. -/
theorem signed_interpolation (r : R.Raw) (hr : r.WellFormed) :
    R.value (K:=K) r=(-1 : K)^r.signs.length *
      (∑k ∈ Finset.range (r.signs.length+1),R.value (K:=K) (W.expand r k)*
        (Lagrange.basis (Finset.range (r.signs.length+1))
          (fun j : ℕ=>(2 : K)^j) k).eval (-1)) := by
  rw [signed_eq,S.signed_interpolation]
  simp_rw [expand_value r hr]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeBinaryThreeUnsignedStarGraph
