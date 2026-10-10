import Holant.NetworkGluing
import Holant.NativeNetwork
import Holant.Certificates.FourthRootOdd.NetworkTools

/-! Ordinary-boundary partial gluing retains the second network's final m
ports, every old scalar component, and one explicitly oriented new edge per
first-boundary port. This does not assert unrestricted free-stub substitution. -/
namespace Holant.ReedMuller.TwoChart.NetworkPlug
open Holant
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} {n m : ℕ}

abbrev Edges (L : Network K n) (R : Network K (n+m)) :=
  (Fin L.shape.edges ⊕ Fin R.shape.edges) ⊕ Fin n

def ports (EL ER : Type*) (n m : ℕ) :
    ((Fin n ⊕ (EL×Bool)) ⊕ ((Fin n ⊕ Fin m) ⊕ (ER×Bool))) ≃
      (Fin m ⊕ (((EL⊕ER)⊕Fin n)×Bool)) where
  toFun
    | .inl (.inl i) => .inr (.inr i,false)
    | .inl (.inr (e,b)) => .inr (.inl (.inl e),b)
    | .inr (.inl (.inl i)) => .inr (.inr i,true)
    | .inr (.inl (.inr i)) => .inl i
    | .inr (.inr (e,b)) => .inr (.inl (.inr e),b)
  invFun
    | .inl i => .inr (.inl (.inr i))
    | .inr (.inr i,false) => .inl (.inl i)
    | .inr (.inr i,true) => .inr (.inl (.inl i))
    | .inr (.inl (.inl e),b) => .inl (.inr (e,b))
    | .inr (.inl (.inr e),b) => .inr (.inr (e,b))
  left_inv := by rintro ((i|⟨e,b⟩)|((i|j)|⟨e,b⟩)) <;> rfl
  right_inv := by
    rintro (i|⟨((e|e)|i),b⟩)
    · rfl
    · cases b <;> rfl
    · cases b <;> rfl
    · cases b <;> rfl

def splitRight (EL ER : Type*) (n m : ℕ) :
    ((Fin n ⊕ (EL×Bool)) ⊕ (Fin (n+m) ⊕ (ER×Bool))) ≃
    ((Fin n ⊕ (EL×Bool)) ⊕ ((Fin n ⊕ Fin m) ⊕ (ER×Bool))) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))

def finite (L : Network K n) (R : Network K (n+m)) (W : Fin n → Bool → Bool → K) :
    FiniteNetwork K (Fin L.shape.vertices⊕Fin R.shape.vertices) (Edges L R) m where
  arity := Sum.elim L.shape.arity R.shape.arity
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports R.shape.ports).trans
      ((splitRight _ _ n m).trans (ports _ _ n m)))
  vertex := fun v => match v with
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e
    | .inr i => W i

def plug (L : Network K n) (R : Network K (n+m)) (W : Fin n → Bool → Bool → K) : Network K m :=
  (finite L R W).toNetwork

@[simp] theorem vertices (L : Network K n) (R : Network K (n+m)) (W : Fin n → Bool → Bool → K) :
    (plug L R W).shape.vertices=L.shape.vertices+R.shape.vertices := by
  simp [plug,FiniteNetwork.toNetwork]
@[simp] theorem edges (L : Network K n) (R : Network K (n+m)) (W : Fin n → Bool → Bool → K) :
    (plug L R W).shape.edges=L.shape.edges+R.shape.edges+n := by
  simp [plug,FiniteNetwork.toNetwork,Edges]

def assignments (L : Network K n) (R : Network K (n+m)) :
    ((Edges L R×Bool)→Bool) ≃
      ((Fin n→Bool)×((Fin n→Bool)×
        (((Fin L.shape.edges×Bool)→Bool)×((Fin R.shape.edges×Bool)→Bool)))) where
  toFun z := (fun i => z (.inr i,false),fun i => z (.inr i,true),
    fun q => z (.inl (.inl q.1),q.2),fun q => z (.inl (.inr q.1),q.2))
  invFun p q := match q with
    | (.inr i,false) => p.1 i
    | (.inr i,true) => p.2.1 i
    | (.inl (.inl e),b) => p.2.2.1 (e,b)
    | (.inl (.inr e),b) => p.2.2.2 (e,b)
  left_inv := by intro z;funext q;rcases q with ⟨((e|e)|i),b⟩ <;> cases b <;> rfl
  right_inv := by intro p;rfl

variable [CommSemiring K]
set_option maxHeartbeats 600000 in
 theorem denote_plug (L : Network K n) (R : Network K (n+m))
    (W : Fin n → Bool → Bool → K) (b : Fin m → Bool) :
    (plug L R W).denote b=
      ∑ x : Fin n→Bool,∑ y : Fin n→Bool,
        L.denote x*R.denote (Fin.addCases y b)*∏ i,W i (x i) (y i) := by
  classical
  let : DecidableEq (Edges L R) := Classical.decEq _
  rw [plug,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : (Edges L R×Bool)→Bool,
    (∏ v,(finite L R W).vertex v (fun i => Sum.elim b z ((finite L R W).ports ⟨v,i⟩)))*
    ∏ e,(finite L R W).edge e (z (e,false)) (z (e,true)))=_
  rw [←(assignments L R).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Network.denote,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  dsimp only [finite]
  simp only [Fintype.prod_sum_type]
  have hl : (fun (v : Fin L.shape.vertices) (i : Fin (L.shape.arity v)) =>
      Sum.elim b ((assignments L R).symm (x,y,zL,zR)) ((finite L R W).ports ⟨.inl v,i⟩))=
      L.shape.assignment x zL := by
    funext v i
    dsimp [finite,NetworkShape.assignment]
    change Sum.elim b ((assignments L R).symm (x,y,zL,zR))
      (ports _ _ n m (splitRight _ _ n m (.inl (L.shape.ports ⟨v,i⟩))))=_
    cases L.shape.ports ⟨v,i⟩ <;> rfl
  have hr : (fun (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v)) =>
      Sum.elim b ((assignments L R).symm (x,y,zL,zR)) ((finite L R W).ports ⟨.inr v,i⟩))=
      R.shape.assignment (Fin.addCases y b) zR := by
    funext v i
    dsimp [finite,NetworkShape.assignment]
    change Sum.elim b ((assignments L R).symm (x,y,zL,zR))
      (ports _ _ n m (splitRight _ _ n m (.inr (R.shape.ports ⟨v,i⟩))))=_
    cases hp : R.shape.ports ⟨v,i⟩ with
    | inr q => rfl
    | inl k =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
        simp [splitRight,ports,assignments]
  dsimp [assignments]
  dsimp [finite,assignments] at hl hr
  simp only [congrFun₂ hl,congrFun₂ hr]
  ac_rfl

 theorem denote_plug_equality (L : Network K n) (R : Network K (n+m)) (b : Fin m→Bool) :
    (plug L R (fun _ => Signature.equality)).denote b=
      ∑ x : Fin n→Bool,L.denote x*R.denote (Fin.addCases x b) := by
  classical
  rw [denote_plug]
  simp only [Signature.prod_equality]
  simp


 theorem denote_plug_disequality (L : Network K n) (R : Network K (n+m)) (b : Fin m→Bool) :
    (plug L R (fun _ => Signature.disequality)).denote b=
      ∑ y : Fin n→Bool,L.denote (fun i => !(y i))*R.denote (Fin.addCases y b) := by
  classical
  rw [denote_plug,Finset.sum_comm]
  simp only [Signature.prod_disequality,mul_ite,mul_one,mul_zero]
  simp

 theorem vertex_mem (A : SignatureFamily K) (L : Network K n) (R : Network K (n+m))
    (W : Fin n→Bool→Bool→K)
    (hL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈A)
    (hR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈A) :
    ∀v,(⟨(plug L R W).shape.arity v,(plug L R W).vertex v⟩ : AnySignature K)∈A := by
  intro v
  change (⟨(finite L R W).arity ((Fintype.equivFin (Fin L.shape.vertices⊕Fin R.shape.vertices)).symm v),
    (finite L R W).vertex ((Fintype.equivFin (Fin L.shape.vertices⊕Fin R.shape.vertices)).symm v)⟩ : AnySignature K)∈A
  cases (Fintype.equivFin (Fin L.shape.vertices⊕Fin R.shape.vertices)).symm v with
  | inl v => exact hL v
  | inr v => exact hR v

 theorem native_edges (L : Network K n) (R : Network K (n+m))
    (hL : ∀e,L.edge e=Signature.disequality) (hR : ∀e,R.edge e=Signature.disequality) :
    ∀e,(plug L R (fun _ => Signature.disequality)).edge e=Signature.disequality := by
  intro e
  change (finite L R (fun _ => Signature.disequality)).edge
    ((Fintype.equivFin (Edges L R)).symm e)=_
  rcases (Fintype.equivFin (Edges L R)).symm e with ((e|e)|i)
  · exact hL e
  · exact hR e
  · rfl

 def withInput (f : Signature K n) (R : Network K (n+m)) : Network K m :=
  plug (Certificates.FourthRootOdd.singleVertexNetwork f) R (fun _ => Signature.disequality)

 theorem withInput_denote (f : Signature K n) (R : Network K (n+m)) (b : Fin m→Bool) :
    (withInput f R).denote b=
      ∑y : Fin n→Bool,f (fun i => !(y i))*R.denote (Fin.addCases y b) := by
  rw [withInput,denote_plug_disequality,Certificates.FourthRootOdd.singleVertexNetwork_denote]

 theorem withInput_vertices (f : Signature K n) (R : Network K (n+m)) :
    (withInput f R).shape.vertices=1+R.shape.vertices := vertices _ _ _

 theorem withInput_edges (f : Signature K n) (R : Network K (n+m)) :
    (withInput f R).shape.edges=R.shape.edges+n := by
  rw [withInput,edges]
  simp [Certificates.FourthRootOdd.singleVertexNetwork]

 theorem withInput_uses (A : SignatureFamily K) (f : Signature K n) (R : Network K (n+m))
    (hR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈A) :
    ∀v,(⟨(withInput f R).shape.arity v,(withInput f R).vertex v⟩ : AnySignature K)∈
      insert (⟨n,f⟩ : AnySignature K) A := by
  apply vertex_mem
  · intro v
    exact Set.mem_insert _ _
  · intro v
    exact Set.mem_insert_of_mem _ (hR v)

 theorem withInput_native (f : Signature K n) (R : Network K (n+m))
    (hR : ∀e,R.edge e=Signature.disequality) :
    ∀e,(withInput f R).edge e=Signature.disequality := by
  apply native_edges _ _ _ hR
  intro e
  exact Fin.elim0 e

end
end Holant.ReedMuller.TwoChart.NetworkPlug
