import Holant.Proofs.Reductions.SingleWeightCompletion.CompletedGraph
import Holant.Complexity.ClosedNetworkCompleteness
import Holant.NativeNetwork


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.CompletedGraph
open Holant.Complexity
open scoped BigOperators
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val)) (d : Fin s → ℕ)
variable (r : Input (s:=s) (a:=a)) (h : Balanced d r)

def network : Network K 0 where
  shape := shape d r h
  vertex v := completed (G (label r v)) (d (label r v))
  edge _ := Signature.disequality
def splitChoice : (Fin (r.val.edges.length+newCount d r) → Bool) ≃
    (Fin r.val.edges.length → Bool) × (Fin (newCount d r) → Bool) where
  toFun c := (fun e => c (Fin.castAdd _ e),fun e => c (Fin.natAdd _ e))
  invFun c := Fin.addCases c.1 c.2
  left_inv c := by funext e; refine Fin.addCases (fun _ => by simp) (fun _ => by simp) e
  right_inv c := by ext e <;> simp

def localWord (c : Fin (r.val.edges.length+newCount d r) → Bool) (v : Fin r.val.vertices.length) :=
  (shape d r h).assignment Fin.elim0 (Network.endpointChoiceAssignment c) v
theorem old_word (x : Fin r.val.edges.length → Bool) (y : Fin (newCount d r) → Bool)
    (v : Fin r.val.vertices.length) :
    restrict (d (label r v)) (localWord d r h (Fin.addCases x y) v) =
      (r.val.shape r.property).assignment Fin.elim0 (Network.endpointChoiceAssignment x) v := by
  funext i
  change Network.endpointChoiceAssignment (Fin.addCases x y)
    (incidence d r h ⟨v,Fin.castAdd (added d r v) i⟩) =
    Network.endpointChoiceAssignment x (r.val.route r.property ⟨v,i⟩)
  rw [original_port]
  simp [Network.endpointChoiceAssignment]
theorem new_word (x : Fin r.val.edges.length → Bool) (y : Fin (newCount d r) → Bool)
    (p : slots d r) :
    localWord d r h (Fin.addCases x y) p.1 (Fin.natAdd (a (label r p.1).val) p.2) =
      if side d r p.1 then y (addedRoute d r h p).1 else !(y (addedRoute d r h p).1) := by
  change Network.endpointChoiceAssignment (Fin.addCases x y)
    (incidence d r h ⟨p.1,Fin.natAdd (a (label r p.1).val) p.2⟩) = _
  rw [appended_port]
  simp [Network.endpointChoiceAssignment]
theorem all_new_pinned (x : Fin r.val.edges.length → Bool) (v : Fin r.val.vertices.length) :
    Pinned (d (label r v)) (localWord d r h (Fin.addCases x (fun _ => true)) v) := by
  intro j
  rw [new_word d r h x (fun _ => true) ⟨v,j⟩]
  change (if side d r v then true else !true) = side d r v
  cases side d r v <;> rfl

/-- Each added tensor entry and edge entry equals one, not merely a nonzero
scale that would need division or a field enlargement. -/
theorem pin_factor_one (v : Fin r.val.vertices.length) :
    Signature.unaryPower (Signature.pointMass (K:=K) (side d r v)) (added d r v)
      (fun _ => side d r v)=1 := by
  rw [Signature.unaryPower_pointMass]
  simp
theorem fresh_edge_factor_one (x : Fin r.val.edges.length → Bool) (e : Fin (newCount d r)) :
    Signature.disequality (K:=K)
      (Network.endpointChoiceAssignment (Fin.addCases x (fun _ => true)) (Fin.natAdd r.val.edges.length e,false))
      (Network.endpointChoiceAssignment (Fin.addCases x (fun _ => true)) (Fin.natAdd r.val.edges.length e,true))=1 := by
  simp [Network.endpointChoiceAssignment,Signature.disequality]

def oldTerm (x : Fin r.val.edges.length → Bool) : K :=
  ∏ v, G (label r v) ((r.val.shape r.property).assignment Fin.elim0 (Network.endpointChoiceAssignment x) v)
def newTerm (c : Fin (r.val.edges.length+newCount d r) → Bool) : K :=
  ∏ v, completed (G (label r v)) (d (label r v)) (localWord d r h c v)

theorem good_term (x : Fin r.val.edges.length → Bool) :
    newTerm G d r h (Fin.addCases x (fun _ => true)) = oldTerm G r x := by
  apply Finset.prod_congr rfl
  intro v _
  rw [completed_apply,if_pos (all_new_pinned d r h x v),old_word]

theorem bad_term (x : Fin r.val.edges.length → Bool) (y : Fin (newCount d r) → Bool)
    (hy : y ≠ fun _ => true) : newTerm G d r h (Fin.addCases x y) = 0 := by
  obtain ⟨e,he⟩ := Function.ne_iff.mp hy
  let p := (addedRoute d r h).symm (e,true)
  have hb : side d r p.1=true := paired_pin d r h e true
  have hr : addedRoute d r h p=(e,true) := (addedRoute d r h).apply_symm_apply _
  apply Finset.prod_eq_zero (Finset.mem_univ p.1)
  rw [completed_apply,if_neg]
  intro hp
  have hpj := hp p.2
  rw [new_word,hr,hb] at hpj
  change y e=side d r p.1 at hpj
  exact he (hpj.trans hb)

theorem term_identity (x : Fin r.val.edges.length → Bool) (y : Fin (newCount d r) → Bool) :
    newTerm G d r h (Fin.addCases x y) = if y=(fun _ => true) then oldTerm G r x else 0 := by
  by_cases hy : y=(fun _ => true)
  · subst y
    simp [good_term]
  · rw [if_neg hy,bad_term G d r h x y hy]

theorem unique_nonzero_extension (x : Fin r.val.edges.length → Bool) (hx : oldTerm G r x ≠ 0) :
    ∃! c : Fin (r.val.edges.length+newCount d r) → Bool,
      (splitChoice d r c).1=x ∧ newTerm G d r h c ≠ 0 := by
  refine ⟨Fin.addCases x (fun _ => true),⟨by funext e; simp [splitChoice],by simpa [good_term] using hx⟩,?_⟩
  intro c hc
  have he : c = Fin.addCases (splitChoice d r c).1 (splitChoice d r c).2 :=
    ((splitChoice d r).symm_apply_apply c).symm
  have hfirst := hc.1
  have hnz := hc.2
  rw [he,term_identity] at hnz
  have hy : (splitChoice d r c).2=(fun _ => true) := by
    by_contra hy
    simp [hy] at hnz
  rw [he,hfirst,hy]

theorem network_value : (network G d r h).denote Fin.elim0 =
    (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  unfold network RawClosedNetwork.realize
  rw [Network.denote_disequality,Network.denote_disequality]
  change (∑ c, newTerm G d r h c) = ∑ x, oldTerm G r x
  rw [←(splitChoice d r).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [splitChoice,Equiv.coe_fn_symm_mk,term_identity]
  simp

private theorem signature_apply_eq {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (hf : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (hmn : m=n) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast hmn i))=g x := by
  subst n
  have he : f=g := eq_of_heq (Sigma.mk.inj_iff.mp hf).2
  subst g
  rfl

theorem labelling_network : (labelling d r h).sourceNetwork (table G d) (fun _ => Signature.disequality) =
    network G d r h := by
  unfold ClosedLabelling.sourceNetwork network
  congr 1
  funext v x
  exact signature_apply_eq (table G d (label r v))
    (completed (G (label r v)) (d (label r v)))
    ((table_label G d (label r v)).trans
      (completed_exact (G (label r v)) (d (label r v))).symm)
    ((labelling d r h).vertex_arity v) x
theorem query_value : ((query d r h).val.realize (query d r h).property (table G d)
    (fun _ => Signature.disequality)).denote Fin.elim0 =
      (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [ClosedLabelling.denote_serialize,labelling_network,network_value]

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.CompletedGraph
