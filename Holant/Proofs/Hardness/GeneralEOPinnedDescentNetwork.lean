import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Tractability.EOEvaluation.PairingConstruction
import Holant.ReedMuller.TwoChart.NetworkPlug

/-! Physical operations for EO descent. Partial gluing keeps the actual input
network, all its labels, and all scalars. The pin bank consists solely of
literal directed 01 vertices and has a proved singleton denotation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace P
export Holant.ReedMuller.TwoChart.NetworkPlug
  (Edges finite plug vertices edges denote_plug_disequality native_edges)
end P
namespace LN
export LabelledNetwork (Exact count)
end LN
namespace PC
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction
  (pairing port_false port_true twice_count matching)
end PC
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} {n m s : ℕ} {a : ℕ → ℕ}

def reboundary (N : Network K n) (e : Fin n ≃ Fin m) : Network K m where
  shape := { vertices := N.shape.vertices
             arity := N.shape.arity
             edges := N.shape.edges
             ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

def reboundaryLabels (N : Network K n) (L : Labelling N.shape s 1 a)
    (e : Fin n ≃ Fin m) : Labelling (reboundary N e).shape s 1 a :=
  ⟨L.vertex,L.vertex_arity,L.edge⟩

theorem reboundary_denote [CommSemiring K] (N : Network K n) (e : Fin n ≃ Fin m) :
    (reboundary N e).denote=Tensor.reindex e N.denote := by
  funext x
  unfold Network.denote Tensor.reindex
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  dsimp [NetworkShape.assignment,reboundary]
  cases N.shape.ports ⟨v,i⟩ <;> rfl

def plugLabels (L : Network K n) (R : Network K (n+m))
    (hL : Labelling L.shape s 1 a) (hR : Labelling R.shape s 1 a)
    (W : Fin n → Bool → Bool → K) : Labelling (P.plug L R W).shape s 1 a where
  vertex v := Sum.elim hL.vertex hR.vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)
  vertex_arity v := by
    change a (Sum.elim hL.vertex hR.vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)).val=
        Sum.elim L.shape.arity R.shape.arity
          ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)
    cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => exact hL.vertex_arity v
    | inr v => exact hR.vertex_arity v
  edge _ := 0

theorem plug_exact (G : (i : Fin s) → Signature K (a i.val))
    (L : Network K n) (R : Network K (n+m))
    (hL : Labelling L.shape s 1 a) (hR : Labelling R.shape s 1 a)
    (eL : LN.Exact G L hL) (eR : LN.Exact G R hR)
    (W : Fin n → Bool → Bool → K) :
    LN.Exact G (P.plug L R W) (plugLabels L R hL hR W) := by
  intro v
  change (⟨a (Sum.elim hL.vertex hR.vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)).val,
      G (Sum.elim hL.vertex hR.vertex
        ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v))⟩ : AnySignature K)=
    ⟨(P.finite L R W).arity ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v),
      (P.finite L R W).vertex ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩
  cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
  | inl v => exact eL v
  | inr v => exact eR v

theorem plug_count (L : Network K n) (R : Network K (n+m))
    (hL : Labelling L.shape s 1 a) (hR : Labelling R.shape s 1 a)
    (W : Fin n → Bool → Bool → K) (j : Fin s) :
    LN.count (plugLabels L R hL hR W) j=LN.count hL j+LN.count hR j := by
  unfold LN.count
  calc
    _ = ∑ v : Fin L.shape.vertices ⊕ Fin R.shape.vertices,
        if Sum.elim hL.vertex hR.vertex v=j then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm
      intro v
      rfl
    _ = _ := by simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

def singletonData (w : Fin n → Bool) (hw : 2*weight w=n) :
    Holant.LocalDrafts.Tractability.EOEvaluation.PairingCharacters.Data n where
  points := {w}
  base := ⟨w,by simp⟩
  closed := by
    intro x hx y hy z hz
    simp only [Finset.mem_singleton] at hx hy hz ⊢
    subst x; subst y; subst z
    funext i
    simp [Holant.Tractable.tripleXor]
  central := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    unfold charge
    omega

def pairing (w : Fin n → Bool) (hw : 2*weight w=n) := PC.pairing (singletonData w hw)

theorem pairing_oriented (w : Fin n → Bool) (hw : 2*weight w=n)
    (i : Fin (pairing w hw).count) (b : Bool) :
    w ((pairing w hw).ports (i,b))=b := by
  cases b
  · exact ((Fintype.equivFin
      (Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction.Side
        (singletonData w hw) false)).symm i).property
  · exact (PC.matching (singletonData w hw) ((Fintype.equivFin
      (Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction.Side
        (singletonData w hw) false)).symm i)).property

variable [CommSemiring K]

def flip : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b

def directed01 : Signature K 2 := fun x => if x 0=false ∧ x 1=true then 1 else 0

/-- One directed 01 vertex for each zero/one pair. Local port order is
reversed at the boundary so the bank supplies the complement of w. -/
def bank (w : Fin n → Bool) (hw : 2*weight w=n) : Network K n where
  shape := {
    vertices := (pairing w hw).count
    arity _ := 2
    edges := 0
    ports := (Equiv.sigmaEquivProd _ _).trans
      ((Equiv.prodCongr (Equiv.refl _) (finTwoEquiv.trans flip)).trans
        ((pairing w hw).ports.trans (Equiv.sumEmpty (Fin n) (Fin 0×Bool)).symm)) }
  vertex _ := directed01
  edge e := Fin.elim0 e

@[simp] theorem bank_vertices (w : Fin n → Bool) (hw : 2*weight w=n) :
    2*(bank (K:=K) w hw).shape.vertices=n := PC.twice_count (singletonData w hw)
@[simp] theorem bank_edges (w : Fin n → Bool) (hw : 2*weight w=n) :
    (bank (K:=K) w hw).shape.edges=0 := rfl

theorem bank_denote (w : Fin n → Bool) (hw : 2*weight w=n) (x : Fin n → Bool) :
    (bank (K:=K) w hw).denote x=if x=(fun i => !(w i)) then 1 else 0 := by
  classical
  have hp : (∀v : Fin (pairing w hw).count,
      x ((pairing w hw).ports (v,true))=false ∧
      x ((pairing w hw).ports (v,false))=true) ↔ x=(fun i => !(w i)) := by
    constructor
    · intro hx
      funext i
      obtain ⟨⟨v,b⟩,rfl⟩ := (pairing w hw).ports.surjective i
      rw [pairing_oriented w hw]
      cases b
      · exact (hx v).2
      · exact (hx v).1
    · intro hx v
      simp only [hx,pairing_oriented w hw,Bool.not_true,Bool.not_false,and_self]
  change (∑z : (Fin 0×Bool) → Bool,
    (∏v : Fin (pairing w hw).count,
      if x ((pairing w hw).ports (v,true))=false ∧
        x ((pairing w hw).ports (v,false))=true then (1 : K) else 0)*
      ∏e : Fin 0,(Fin.elim0 e : Bool → Bool → K) (z (e,false)) (z (e,true)))=_
  simp only [Fintype.prod_empty,mul_one,Fintype.sum_unique,Fintype.prod_boole,hp]

def bankLabels (w : Fin n → Bool) (hw : 2*weight w=n) (j : Fin s) (hj : a j.val=2) :
    Labelling (bank (K:=K) w hw).shape s 1 a where
  vertex _ := j
  vertex_arity _ := hj
  edge e := Fin.elim0 e

theorem bank_exact (G : (i : Fin s) → Signature K (a i.val))
    (w : Fin n → Bool) (hw : 2*weight w=n) (j : Fin s)
    (hj : (⟨a j.val,G j⟩ : AnySignature K)=⟨2,directed01⟩) :
    LN.Exact G (bank w hw) (bankLabels w hw j (congrArg Sigma.fst hj)) := fun _ => hj

theorem bank_count (w : Fin n → Bool) (hw : 2*weight w=n) (j : Fin s) (hj : a j.val=2)
    (k : Fin s) : LN.count (bankLabels (K:=K) w hw j hj) k=
      if j=k then (pairing w hw).count else 0 := by
  by_cases h : j=k <;> simp [LN.count,LabelledNetwork.count,bankLabels,h,bank]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentNetwork
