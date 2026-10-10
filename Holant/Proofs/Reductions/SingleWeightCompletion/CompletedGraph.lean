import Holant.Proofs.Reductions.SingleWeightCompletion.SlotRouting
import Holant.Complexity.ClosedNetworkSerialize


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.CompletedGraph
open Holant.Complexity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ} (d : Fin s → ℕ) (r : Input (s:=s) (a:=a))
def label (v : Fin r.val.vertices.length) : Fin s := r.val.signatureLabel r.property v
def added (v : Fin r.val.vertices.length) : ℕ := extra (a (label r v).val) (d (label r v))
def side (v : Fin r.val.vertices.length) : Bool := pin (a (label r v).val) (d (label r v))
def color (v : Fin r.val.vertices.length) : Fin r.val.vertices.length := (r.val.graph r.property).label v
abbrev slots := SlotRouting.Slot (added d r)
abbrev newCount := SlotRouting.total (added d r) (side d r) (color r)

theorem all_charges (h : Balanced d r) (c : ℕ) : componentCharge d r c=0 := by
  by_cases he : ∃ v, component r v=c
  · obtain ⟨v,rfl⟩ := he
    exact h v
  · apply Finset.sum_eq_zero
    intro v _
    exact if_neg (fun hv => he ⟨v,hv⟩)
theorem slot_balance (h : Balanced d r) : SlotRouting.Balanced (added d r) (side d r) (color r) := by
  intro c
  have he : (SlotRouting.size (added d r) (side d r) (color r) c false:ℤ) -
      SlotRouting.size (added d r) (side d r) (color r) c true = componentCharge d r c.val := by
    simp only [SlotRouting.size,componentCharge,Nat.cast_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : color r v=c
    · have hv' : component r v=c.val := congrArg Fin.val hv
      have hp := charge_extra (a (label r v).val) (d (label r v))
      change chargeAt d r v =
        if side d r v then -(added d r v : ℤ) else (added d r v : ℤ) at hp
      rw [if_pos hv', hp]
      cases hb : side d r v <;> simp [SlotRouting.mass,hv,hb]
    · have hv' : component r v≠c.val := fun he => hv (Fin.ext he)
      simp [SlotRouting.mass,hv,hv']
  rw [all_charges d r h c.val] at he
  omega

variable (h : Balanced d r)
abbrev addedRoute := SlotRouting.numbered (added d r) (side d r) (color r) (slot_balance d r h)
def splitPorts : (Σ v : Fin r.val.vertices.length, Fin (a (label r v).val+added d r v)) ≃
    r.val.Ports a ⊕ slots d r :=
  (Equiv.sigmaCongrRight (fun v => finSumFinEquiv.symm)).trans (Equiv.sigmaSumDistrib _ _)
def incidence : (Σ v : Fin r.val.vertices.length, Fin (a (label r v).val+added d r v)) ≃
    Fin (r.val.edges.length+newCount d r) × Bool :=
  (splitPorts d r).trans
    ((Equiv.sumCongr (r.val.portEquiv r.property) (addedRoute d r h)).trans
      ((Equiv.sumProdDistrib _ _ Bool).symm.trans
        (Equiv.prodCongr finSumFinEquiv (Equiv.refl Bool))))
def shape : NetworkShape 0 where
  vertices := r.val.vertices.length
  arity v := a (label r v).val+added d r v
  edges := r.val.edges.length+newCount d r
  ports := (incidence d r h).trans (RawClosedNetwork.closedEndsEquiv _)
def labelling : ClosedLabelling (shape d r h) s 1 (arity (a:=a) d) where
  vertex := label r
  vertex_arity v := by simp [arity,label,added,(label r v).isLt,shape]
  edge _ := 0
def query : ExactSignatureTables.Input s 1 (arity (a:=a) d) := (labelling d r h).validated

theorem original_port (v : Fin r.val.vertices.length) (i : Fin (a (label r v).val)) :
    incidence d r h ⟨v,Fin.castAdd (added d r v) i⟩ =
      (Fin.castAdd (newCount d r) (r.val.route r.property ⟨v,i⟩).1,(r.val.route r.property ⟨v,i⟩).2) := by
  simp [incidence,splitPorts,Equiv.sigmaCongrRight,Equiv.sigmaSumDistrib,
    Equiv.sumProdDistrib,RawClosedNetwork.portEquiv]
  rfl
theorem appended_port (v : Fin r.val.vertices.length) (i : Fin (added d r v)) :
    incidence d r h ⟨v,Fin.natAdd (a (label r v).val) i⟩ =
      (Fin.natAdd r.val.edges.length (addedRoute d r h ⟨v,i⟩).1,side d r v) := by
  simp [incidence,splitPorts,Equiv.sigmaCongrRight,Equiv.sigmaSumDistrib,
    Equiv.sumProdDistrib,SlotRouting.route_side]
  rfl
theorem fresh (p : slots d r) : r.val.edges.length ≤
    (incidence d r h ⟨p.1,Fin.natAdd (a (label r p.1).val) p.2⟩).1.val := by
  rw [appended_port]
  simp
theorem paired_component (e : Fin (newCount d r)) :
    color r ((addedRoute d r h).symm (e,false)).1 = color r ((addedRoute d r h).symm (e,true)).1 :=
  SlotRouting.same_component _ _ _ _ e
theorem paired_pin (e : Fin (newCount d r)) (b : Bool) :
    side d r ((addedRoute d r h).symm (e,b)).1 = b := SlotRouting.prescribed_bit _ _ _ _ e b

theorem wellFormed : (query d r h).val.WellFormed s 1 (arity (a:=a) d) := (query d r h).property
theorem vertex_count : (query d r h).val.vertices.length=r.val.vertices.length := List.length_ofFn
theorem edge_count : (query d r h).val.edges.length=r.val.edges.length+newCount d r := List.length_ofFn

def row (v : Fin r.val.vertices.length) : RawVertex :=
  ((r.val.vertices.get v).1,(r.val.vertices.get v).2 ++
    List.ofFn (fun i : Fin (added d r v) =>
      (r.val.edges.length+(addedRoute d r h ⟨v,i⟩).1.val,side d r v)))
theorem rows_exact : (query d r h).val.vertices=List.ofFn (row d r h) := by
  apply congrArg List.ofFn
  funext v
  unfold row
  apply Prod.ext
  · rfl
  · change List.ofFn (fun i : Fin (a (label r v).val+added d r v) =>
      ((incidence d r h ⟨v,i⟩).1.val,(incidence d r h ⟨v,i⟩).2)) =
      (r.val.vertices.get v).2 ++ List.ofFn (fun i : Fin (added d r v) =>
        (r.val.edges.length+(addedRoute d r h ⟨v,i⟩).1.val,side d r v))
    rw [List.ofFn_add]
    congr 1
    · apply List.ext_getElem
      · simpa only [List.length_ofFn,label,RawClosedNetwork.signatureLabel] using (r.property.1 v).2.symm
      · intro i hi hj
        have hi' : i < a (label r v).val := by simpa only [List.length_ofFn] using hi
        have hp := congrArg (fun p : Fin (r.val.edges.length+newCount d r) × Bool => (p.1.val,p.2))
          (original_port d r h v ⟨i,hi'⟩)
        simpa [RawClosedNetwork.route,RawClosedNetwork.portEndpoint] using hp
    · apply congrArg List.ofFn
      funext i
      simp [appended_port,row]
theorem edges_exact : (query d r h).val.edges=List.replicate (r.val.edges.length+newCount d r) 0 := by
  simp [query,labelling,ClosedLabelling.validated,ClosedLabelling.serialize,shape]

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.CompletedGraph
