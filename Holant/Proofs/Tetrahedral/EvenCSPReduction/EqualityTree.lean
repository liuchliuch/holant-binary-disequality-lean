import Holant.Proofs.Tetrahedral.EvenCSPReduction.Incidence
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.EqualityTree
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.EightVertex.ProductAnchor
open scoped BigOperators

abbrev Ports (t : ℕ) := Σ _ : Fin (t+1),Fin 4
abbrev Ends (t : ℕ) := Fin (2*t+4) ⊕ (Fin t × Bool)

/-- Exactly the original four ports of each Eq4, in their stored order.
Each next node replaces the preceding final boundary by a true/false
internal pair and exposes three new consecutive boundary occurrences. -/
def port (t : ℕ) (p : Ports t) : Ends t :=
  if p.2.val=0 then
    if h : p.1.val=0 then .inl ⟨0,by omega⟩
    else .inr (⟨p.1.val-1,by have := p.1.isLt; omega⟩,true)
  else if p.2.val=1 then .inl ⟨2*p.1.val+1,by have := p.1.isLt; omega⟩
  else if p.2.val=2 then .inl ⟨2*p.1.val+2,by have := p.1.isLt; omega⟩
  else if h : p.1.val=t then .inl ⟨2*t+3,by omega⟩
  else .inr (⟨p.1.val,by have := p.1.isLt; omega⟩,false)

def literalPort (t : ℕ) (v i : ℕ) : LocalEndpoint :=
  if i=0 then (if v=0 then .inl 0 else .inr (v-1,true))
  else if i=1 then .inl (2*v+1)
  else if i=2 then .inl (2*v+2)
  else if v=t then .inl (2*t+3) else .inr (v,false)

theorem embed_port (t : ℕ) (p : Ports t) :
    Template.embed (2*t+4) t (port t p)=literalPort t p.1.val p.2.val := by
  unfold port literalPort
  split_ifs <;> rfl

theorem port_injective (t : ℕ) : Function.Injective (port t) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hc := congrArg (Template.embed (2*t+4) t) h
  rw [embed_port,embed_port] at hc
  have hv := v.isLt
  have hw := w.isLt
  fin_cases i <;> fin_cases j <;>
    simp only [literalPort] at hc <;>
    split_ifs at hc <;>
    simp only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Bool.false_eq_true,Bool.true_eq_false,and_false,false_and] at hc
  all_goals
    first
    | contradiction
    | exact False.elim (by omega)
    | apply Sigma.ext (Fin.ext (by change v.val=w.val; omega)); rfl

theorem ports_card (t : ℕ) : Fintype.card (Ports t)=Fintype.card (Ends t) := by
  simp [Ports,Ends,Fintype.card_sigma]
  omega

def ports (t : ℕ) : Ports t ≃ Ends t :=
  Equiv.ofBijective (port t) ⟨port_injective t,
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq (ports_card t))).mp
      (port_injective t)⟩

def shape (t : ℕ) : NetworkShape (2*t+4) where
  vertices := t+1
  arity _ := 4
  edges := t
  ports := ports t

def graph {K : Type*} [CommSemiring K] (t : ℕ) : Network K (2*t+4) where
  shape := shape t
  vertex _ := equalityFour
  edge _ := Signature.equality

@[simp] theorem graph_vertices {K : Type*} [CommSemiring K] (t : ℕ) :
    (graph (K:=K) t).shape.vertices=t+1 := rfl
@[simp] theorem graph_edges {K : Type*} [CommSemiring K] (t : ℕ) :
    (graph (K:=K) t).shape.edges=t := rfl

def bits (t : ℕ) (x : Fin (2*t+4) → Bool) (c : Fin t → Bool)
    (v : Fin (t+1)) (i : Fin 4) : Bool :=
  Sum.elim x (fun p => c p.1) (port t ⟨v,i⟩)

theorem root_bit (t : ℕ) (x : Fin (2*t+4) → Bool) (c : Fin t → Bool) :
    bits t x c 0 0=x 0 := by simp [bits,port]

theorem previous_bit (t : ℕ) (x : Fin (2*t+4) → Bool) (c : Fin t → Bool)
    (e : Fin t) : bits t x c e.castSucc 3=c e := by
  have hn : e.val≠t := Nat.ne_of_lt e.isLt
  simp [bits,port,hn]

theorem successor_bit (t : ℕ) (x : Fin (2*t+4) → Bool) (c : Fin t → Bool)
    (e : Fin t) : bits t x c e.succ 0=c e := by
  simp [bits,port]

/-- Both directions of support. Every boundary occurrence and every actual
internal edge is forced to the same root bit; no branch is lost or doubled. -/
theorem support_iff (t : ℕ) (x : Fin (2*t+4) → Bool) (c : Fin t → Bool) :
    (∀v : Fin (t+1),∀i : Fin 4,bits t x c v i=bits t x c v 0) ↔
      (∀i : Fin (2*t+4),x i=x 0) ∧ (∀e : Fin t,c e=x 0) := by
  constructor
  · intro h
    have hv : ∀v : Fin (t+1),bits t x c v 0=x 0 := by
      intro v
      refine Fin.induction (root_bit t x c) ?_ v
      intro e ih
      rw [successor_bit t x c e,←previous_bit t x c e]
      exact (h e.castSucc 3).trans ih
    constructor
    · intro i
      let p := (ports t).symm (.inl i)
      have hp : bits t x c p.1 p.2=x i := by
        change Sum.elim x (fun q => c q.1) ((ports t) p)=x i
        rw [Equiv.apply_symm_apply]
        rfl
      exact hp.symm.trans ((h p.1 p.2).trans (hv p.1))
    · intro e
      let p := (ports t).symm (.inr (e,false))
      have hp : bits t x c p.1 p.2=c e := by
        change Sum.elim x (fun q => c q.1) ((ports t) p)=c e
        rw [Equiv.apply_symm_apply]
        rfl
      exact hp.symm.trans ((h p.1 p.2).trans (hv p.1))
  · rintro ⟨hx,hc⟩ v i
    have hall (v : Fin (t+1)) (j : Fin 4) : bits t x c v j=x 0 := by
      unfold bits
      cases port t ⟨v,j⟩ with
      | inl j => exact hx j
      | inr q => exact hc q.1
    exact (hall v i).trans (hall v 0).symm

def doubled (E : Type*) : ((E×Bool)→Bool) ≃ ((E→Bool)×(E→Bool)) where
  toFun z := (fun e => z (e,false),fun e => z (e,true))
  invFun z p := if p.2 then z.2 p.1 else z.1 p.1
  left_inv z := by funext p; rcases p with ⟨e,b⟩; cases b <;> rfl
  right_inv z := rfl

/-- The actual ordinary edge product eliminates unequal end assignments.
It leaves one independent bit per edge, with no normalization scalar. -/
theorem ordinary_denote {K : Type*} [CommSemiring K] {n : ℕ}
    (N : Network K n) (hE : ∀e,N.edge e=Signature.equality) (x : Fin n → Bool) :
    N.denote x=∑c : Fin N.shape.edges → Bool,
      ∏v,N.vertex v (N.shape.assignment x (fun p => c p.1) v) := by
  classical
  unfold Network.denote
  rw [←(doubled (Fin N.shape.edges)).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [hE]
  have he (a b : Fin N.shape.edges → Bool) :
      (∏e : Fin N.shape.edges,Signature.equality (K:=K) (a e) (b e))=
        if a=b then 1 else 0 := by
    simp only [Signature.equality,Fintype.prod_boole,←funext_iff]
  simp only [doubled,Equiv.coe_fn_symm_mk,Bool.false_eq_true,if_false,if_true,he]
  simp

def equality {K : Type*} [Zero K] [One K] (n : ℕ) (hn : 0<n) : Signature K n :=
  fun x => if ∀i,x i=x ⟨0,hn⟩ then 1 else 0

/-- Exact Eq(2t+4), from the original t+1 Eq4 occurrences and t Eq edges. -/
theorem denote {K : Type*} [CommSemiring K] (t : ℕ) :
    (graph (K:=K) t).denote=equality (2*t+4) (by omega) := by
  classical
  funext x
  rw [ordinary_denote _ (fun _ => rfl)]
  change (∑c : Fin t → Bool,∏v : Fin (t+1),
    if ∀i : Fin 4,bits t x c v i=bits t x c v 0 then (1 : K) else 0)=_
  simp only [Fintype.prod_boole]
  simp_rw [support_iff]
  have hc (c : Fin t → Bool) : (∀e,c e=x 0) ↔ c=(fun _ => x 0) := by
    exact funext_iff.symm
  simp_rw [hc]
  by_cases hx : ∀i : Fin (2*t+4),x i=x 0 <;> simp [equality,hx]

/-- Local internally supported edge words are bijective with the single
unit choice when the actual boundary is constant. -/
def supported {t : ℕ} (x : Fin (2*t+4) → Bool) :=
  {c : Fin t → Bool // ∀v : Fin (t+1),∀i : Fin 4,bits t x c v i=bits t x c v 0}

theorem unique_internal (t : ℕ) (x : Fin (2*t+4) → Bool)
    (hx : ∀i,x i=x 0) : ∃! c : Fin t → Bool,
      ∀v : Fin (t+1),∀i : Fin 4,bits t x c v i=bits t x c v 0 := by
  refine ⟨(fun _ => x 0),(support_iff t x _).mpr ⟨hx,fun _ => rfl⟩,?_⟩
  intro c hc
  funext e
  exact ((support_iff t x c).mp hc).2 e

/-- One original Eq4 and two actual Eq self-loops. This is the physical
factor two for a declared variable with no occurrences. -/
def zeroGraph {K : Type*} [CommSemiring K] : Network K 0 :=
  ((Network.corolla (equalityFour (K:=K))).contract Signature.equality).contract
    Signature.equality

theorem zeroGraph_denote {K : Type*} [CommSemiring K] :
    (zeroGraph (K:=K)).denote Fin.elim0=2 := by
  rw [zeroGraph,Network.denote_contract,Network.denote_contract,Network.denote_corolla]
  norm_num [Signature.contract,Signature.equality,equalityFour,Fintype.sum_bool,
    Fin.forall_fin_succ]

@[simp] theorem zeroGraph_vertices {K : Type*} [CommSemiring K] :
    (zeroGraph (K:=K)).shape.vertices=1 := rfl
@[simp] theorem zeroGraph_edges {K : Type*} [CommSemiring K] :
    (zeroGraph (K:=K)).shape.edges=2 := rfl

private theorem signature_cast_apply {K : Type*} {m n : ℕ}
    (f : Signature K m) (g : Signature K n)
    (h : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast (congrArg Sigma.fst h) i))=g x := by
  cases h
  rfl

section Labelled
variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val)) (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=⟨4,equalityFour⟩)

def labels (t : ℕ) : Labelling (shape t) s 1 a where
  vertex _ := j4
  vertex_arity _ := congrArg Sigma.fst h4
  edge _ := 0

theorem labelled_denote (t : ℕ) :
    ((labels G j4 h4 t).sourceNetwork G (fun _ : Fin 1 => Signature.equality)).denote=
      equality (2*t+4) (by omega) := by
  rw [←denote t]
  refine Network.denote_congr (shape t) _ _ _ _ ?_ (fun _ _ _ => rfl)
  intro v x
  change G j4 (fun i => x (Fin.cast (congrArg Sigma.fst h4) i))=equalityFour x
  exact signature_cast_apply (G j4) equalityFour h4 x

theorem template_denote (t : ℕ) :
    ((labels G j4 h4 t).template.network (labels G j4 h4 t).wellFormed G
      (fun _ : Fin 1 => Signature.equality)).denote=equality (2*t+4) (by omega) := by
  rw [Labelling.denote_template]
  exact labelled_denote G j4 h4 t

end Labelled
end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.EqualityTree
end
