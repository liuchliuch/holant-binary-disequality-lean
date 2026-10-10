import Holant.ReedMuller.TwoChart.ContextRealizationFlat
import Holant.NetworkTensor

/-! Eliminate literal binary X vertices by two literal I vertices and one
native X edge. This is an incidence-bijection construction on ordinary finite
networks, including loops, parallel edges, and nullary components. -/
namespace Holant.ReedMuller.TwoChart.NativeXExpansion
open Holant
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K : Type*} [CommSemiring K] {n : ℕ}

abbrev IsX (N : Network K n) (v : Fin N.shape.vertices) : Prop :=
  (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)=
    ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩
abbrev Kept (N : Network K n) := {v : Fin N.shape.vertices // ¬IsX N v}
abbrev Split (N : Network K n) := {v : Fin N.shape.vertices // IsX N v}
abbrev Vertices (N : Network K n) := Kept N ⊕ (Split N × Bool)
abbrev Edges (N : Network K n) := Fin N.shape.edges ⊕ Split N

theorem split_arity (N : Network K n) (v : Split N) : N.shape.arity v.1=2 :=
  congrArg Sigma.fst v.2

def splitPort (N : Network K n) (v : Split N) (b : Bool) :
    Fin (N.shape.arity v.1) := Fin.cast (split_arity N v).symm (finTwoEquiv.symm b)

def oldPorts (N : Network K n) :
    (Σv : Fin N.shape.vertices,Fin (N.shape.arity v)) ≃
      ((Σv : Kept N,Fin (N.shape.arity v.1)) ⊕ (Split N × Bool)) where
  toFun p := if h : IsX N p.1 then .inr (⟨p.1,h⟩,finTwoEquiv (Fin.cast (congrArg Sigma.fst h) p.2))
    else .inl ⟨⟨p.1,h⟩,p.2⟩
  invFun
    | .inl ⟨v,i⟩ => ⟨v.1,i⟩
    | .inr (v,b) => ⟨v.1,splitPort N v b⟩
  left_inv := by
    rintro ⟨v,i⟩
    dsimp
    split_ifs with h
    · simp [splitPort]
    · rfl
  right_inv := by
    rintro (⟨v,i⟩|⟨v,b⟩)
    · simp [v.2]
    · dsimp only
      simp only [dite_eq_left v.2,splitPort,Fin.cast_cast,Fin.cast_eq_self,Equiv.apply_symm_apply]

def vertexPorts (N : Network K n) :
    (Σv : Vertices N,Fin (Sum.elim (fun u : Kept N => N.shape.arity u.1) (fun _ => 2) v)) ≃
      (((Σv : Kept N,Fin (N.shape.arity v.1)) ⊕ (Split N × Bool)) ⊕ (Split N × Bool)) where
  toFun
    | ⟨.inl v,i⟩ => .inl (.inl ⟨v,i⟩)
    | ⟨.inr q,i⟩ => if finTwoEquiv i then .inr q else .inl (.inr q)
  invFun
    | .inl (.inl ⟨v,i⟩) => ⟨.inl v,i⟩
    | .inl (.inr q) => ⟨.inr q,(0 : Fin 2)⟩
    | .inr q => ⟨.inr q,(1 : Fin 2)⟩
  left_inv := by
    rintro ⟨v|q,i⟩
    · rfl
    · fin_cases i <;> rfl
  right_inv := by rintro ((⟨v,i⟩|q)|q) <;> rfl

def boundaryPorts (E T : Type*) (n : ℕ) :
    ((Fin n ⊕ (E×Bool)) ⊕ (T×Bool)) ≃ (Fin n ⊕ ((E⊕T)×Bool)) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr (e,b)) => .inr (.inl e,b)
    | .inr (t,b) => .inr (.inr t,b)
  invFun
    | .inl i => .inl (.inl i)
    | .inr (.inl e,b) => .inl (.inr (e,b))
    | .inr (.inr t,b) => .inr (t,b)
  left_inv := by rintro ((i|⟨e,b⟩)|⟨t,b⟩) <;> rfl
  right_inv := by rintro (i|⟨e|t,b⟩) <;> rfl

def finite (N : Network K n) : FiniteNetwork K (Vertices N) (Edges N) n where
  arity := Sum.elim (fun u : Kept N => N.shape.arity u.1) (fun _ => 2)
  ports := (vertexPorts N).trans ((Equiv.sumCongr ((oldPorts N).symm.trans N.shape.ports)
    (Equiv.refl _)).trans (boundaryPorts _ _ n))
  vertex := fun v => match v with
    | .inl u => N.vertex u.1
    | .inr _ => fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1)
  edge := Sum.elim N.edge (fun _ => Signature.disequality)

def expand (N : Network K n) : Network K n := (finite N).toNetwork

@[simp] theorem vertex_count (N : Network K n) :
    (expand N).shape.vertices=Fintype.card (Kept N)+2*Fintype.card (Split N) := by
  simp [expand,FiniteNetwork.toNetwork,Vertices,Nat.mul_comm]
@[simp] theorem edge_count (N : Network K n) :
    (expand N).shape.edges=N.shape.edges+Fintype.card (Split N) := by
  simp [expand,FiniteNetwork.toNetwork,Edges]

theorem partition_count (N : Network K n) :
    Fintype.card (Kept N)+Fintype.card (Split N)=N.shape.vertices := by
  have h := Fintype.card_congr (Equiv.sumCompl (IsX N))
  simpa [Kept,Split,add_comm] using h

theorem vertex_count_exact (N : Network K n) :
    (expand N).shape.vertices=N.shape.vertices+Fintype.card (Split N) := by
  rw [vertex_count]
  have h := partition_count N
  omega

theorem vertex_bound (N : Network K n) : (expand N).shape.vertices≤2*N.shape.vertices := by
  rw [vertex_count]
  have h := partition_count N
  omega

theorem edge_bound (N : Network K n) : (expand N).shape.edges≤N.shape.edges+N.shape.vertices := by
  rw [edge_count]
  have h := partition_count N
  omega


def oldBits (N : Network K n) (x : Fin n→Bool) (z : (Fin N.shape.edges×Bool)→Bool) :
    (Split N×Bool)→Bool := fun q => N.shape.assignment x z q.1.1 (splitPort N q.1 q.2)

theorem split_value {d : ℕ} {f : Signature K d}
    (h : (⟨d,f⟩ : AnySignature K)=⟨2,fun x => Signature.disequality (x 0) (x 1)⟩)
    (x : Fin d→Bool) : f x=Signature.disequality
      (x (Fin.cast (congrArg Sigma.fst h).symm 0))
      (x (Fin.cast (congrArg Sigma.fst h).symm 1)) := by
  cases h
  rfl

theorem old_product (N : Network K n) (x : Fin n→Bool) (z : (Fin N.shape.edges×Bool)→Bool) :
    (∏v,N.vertex v (N.shape.assignment x z v))=
      (∏v : Kept N,N.vertex v.1 (N.shape.assignment x z v.1))*
      ∏t : Split N,Signature.disequality (oldBits N x z (t,false)) (oldBits N x z (t,true)) := by
  rw [←(Equiv.sumCompl (IsX N)).prod_comp]
  simp only [Fintype.prod_sum_type,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  exact split_value v.2 _

theorem kept_assignment (N : Network K n) (x : Fin n→Bool)
    (a : (Fin N.shape.edges×Bool)→Bool) (b : (Split N×Bool)→Bool) (v : Kept N) :
    (fun i => Sum.elim x ((Network.tensorAssignments _ _).symm (a,b))
      ((finite N).ports ⟨.inl v,i⟩))=N.shape.assignment x a v.1 := by
  funext i
  change Sum.elim x ((Network.tensorAssignments _ _).symm (a,b))
    (boundaryPorts _ _ n (.inl (N.shape.ports ⟨v.1,i⟩))) =
      Sum.elim x a (N.shape.ports ⟨v.1,i⟩)
  cases N.shape.ports ⟨v.1,i⟩ <;> rfl

theorem split_assignment (N : Network K n) (x : Fin n→Bool)
    (a : (Fin N.shape.edges×Bool)→Bool) (b : (Split N×Bool)→Bool) (q : Split N×Bool) :
    (finite N).vertex (.inr q) (fun i => Sum.elim x ((Network.tensorAssignments _ _).symm (a,b))
      ((finite N).ports ⟨.inr q,i⟩))=Signature.equality (oldBits N x a q) (b q) := by
  change Signature.equality (Sum.elim x ((Network.tensorAssignments _ _).symm (a,b))
    (boundaryPorts _ _ n (.inl (N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩)))) (b q)=
      Signature.equality (Sum.elim x a (N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩)) (b q)
  cases N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩ <;> rfl

theorem prod_equality {ι : Type*} [Fintype ι] (a b : ι→Bool) :
    (∏i,(Signature.equality (a i) (b i) : K))=if b=a then 1 else 0 := by
  simp only [Signature.equality,Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => (funext h).symm,fun h i => (congrFun h i).symm⟩

set_option maxHeartbeats 600000 in
theorem denote_expand (N : Network K n) : (expand N).denote=N.denote := by
  classical
  let : DecidableEq (Edges N) := Classical.decEq _
  funext x
  rw [expand,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑z : (Edges N×Bool)→Bool,
    (∏v,(finite N).vertex v (fun i => Sum.elim x z ((finite N).ports ⟨v,i⟩)))*
    ∏e,(finite N).edge e (z (e,false)) (z (e,true)))=_
  rw [←(Network.tensorAssignments (Fin N.shape.edges) (Split N)).symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.prod_sum_type,kept_assignment,split_assignment]
  change (∑a : (Fin N.shape.edges×Bool)→Bool,∑b : (Split N×Bool)→Bool,
    ((∏v : Kept N,N.vertex v.1 (N.shape.assignment x a v.1))*
      ∏q : Split N×Bool,Signature.equality (oldBits N x a q) (b q))*
      ((∏e,N.edge e (a (e,false)) (a (e,true)))*
        ∏t : Split N,Signature.disequality (b (t,false)) (b (t,true))))=_
  simp only [prod_equality,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro a _
  rw [old_product]
  ac_rfl


/-- Exact counts when all original occurrences are literal X vertices. -/
theorem all_split_counts (N : Network K n) (h : ∀v,IsX N v) :
    (expand N).shape.vertices=2*N.shape.vertices ∧
    (expand N).shape.edges=N.shape.edges+N.shape.vertices := by
  have hc : Fintype.card (Split N)=N.shape.vertices := by
    simpa using Fintype.card_congr (Equiv.subtypeUnivEquiv h)
  rw [vertex_count_exact,edge_count,hc]
  omega

/-- The replacement has a uniform linear size overhead. -/
theorem size_bound (N : Network K n) :
    (expand N).shape.vertices+(expand N).shape.edges≤3*N.shape.vertices+N.shape.edges := by
  have hv := vertex_bound N
  have he := edge_bound N
  omega

/-- Every old physical port is retained, at port zero of the corresponding
new I vertex precisely when its original X vertex was split. -/
def liftOldPort (N : Network K n) (p : Σv : Fin N.shape.vertices,Fin (N.shape.arity v)) :
    Σv : Vertices N,Fin ((finite N).arity v) :=
  match oldPorts N p with
  | .inl ⟨v,i⟩ => ⟨.inl v,i⟩
  | .inr q => ⟨.inr q,(0 : Fin 2)⟩

theorem old_incidence (N : Network K n) (p : Σv : Fin N.shape.vertices,Fin (N.shape.arity v)) :
    (finite N).ports (liftOldPort N p)=
      Sum.map id (fun q => (Sum.inl q.1,q.2)) (N.shape.ports p) := by
  obtain ⟨q,rfl⟩ := (oldPorts N).symm.surjective p
  cases q with
  | inl q =>
    rcases q with ⟨v,i⟩
    simp only [liftOldPort,Equiv.apply_symm_apply]
    change boundaryPorts _ _ n (.inl (N.shape.ports ⟨v.1,i⟩))=
      Sum.map id (fun q => (Sum.inl q.1,q.2)) (N.shape.ports ⟨v.1,i⟩)
    cases N.shape.ports ⟨v.1,i⟩ <;> rfl
  | inr q =>
    simp only [liftOldPort,Equiv.apply_symm_apply]
    change boundaryPorts _ _ n (.inl (N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩))=
      Sum.map id (fun q => (Sum.inl q.1,q.2)) (N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩)
    cases N.shape.ports ⟨q.1.1,splitPort N q.1 q.2⟩ <;> rfl

/-- The added edge connects the inner ordered ports of the two new I vertices. -/
theorem new_incidence (N : Network K n) (t : Split N) (b : Bool) :
    (finite N).ports ⟨.inr (t,b),(1 : Fin 2)⟩=.inr (.inr t,b) := rfl

def enumeratePort (N : Network K n) :
    (Σv : Vertices N,Fin ((finite N).arity v)) ≃
      (Σv : Fin (expand N).shape.vertices,Fin ((expand N).shape.arity v)) :=
  (Equiv.sigmaCongrLeft (Fintype.equivFin (Vertices N)).symm).symm

def edgeEquiv (N : Network K n) : Edges N ≃ Fin (expand N).shape.edges :=
  Fintype.equivFin (Edges N)

/-- No old edge is contracted or merged, including a loop or a parallel edge. -/
theorem old_edge_incidence (N : Network K n) (e : Fin N.shape.edges) (b : Bool) :
    (expand N).shape.ports (enumeratePort N
      (liftOldPort N (N.shape.ports.symm (.inr (e,b)))))=
      .inr ((edgeEquiv N) (.inl e),b) := by
  change (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr (Fintype.equivFin (Edges N)) (Equiv.refl _)))
      ((finite N).ports ((enumeratePort N).symm (enumeratePort N
        (liftOldPort N (N.shape.ports.symm (.inr (e,b)))))))=_
  rw [Equiv.symm_apply_apply,old_incidence,Equiv.apply_symm_apply]
  rfl

/-- The original numbered output ports keep their numbers. -/
theorem boundary_incidence (N : Network K n) (i : Fin n) :
    (expand N).shape.ports (enumeratePort N
      (liftOldPort N (N.shape.ports.symm (.inl i))))=.inl i := by
  change (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr (Fintype.equivFin (Edges N)) (Equiv.refl _)))
      ((finite N).ports ((enumeratePort N).symm (enumeratePort N
        (liftOldPort N (N.shape.ports.symm (.inl i))))))=_
  rw [Equiv.symm_apply_apply,old_incidence,Equiv.apply_symm_apply]
  rfl

theorem native_edges (N : Network K n) (hN : ∀e,N.edge e=Signature.disequality) :
    ∀e,(expand N).edge e=Signature.disequality := by
  intro e
  change (finite N).edge ((Fintype.equivFin (Edges N)).symm e)=_
  cases (Fintype.equivFin (Edges N)).symm e with
  | inl e => exact hN e
  | inr t => rfl


def vertexEquiv (N : Network K n) : Vertices N ≃ Fin (expand N).shape.vertices :=
  Fintype.equivFin (Vertices N)

/-- Every unsplit vertex is the very same labelled occurrence, after finite
enumeration; this includes all original nullary vertices. -/
theorem kept_label (N : Network K n) (v : Kept N) :
    (⟨(expand N).shape.arity ((vertexEquiv N) (.inl v)),
      (expand N).vertex ((vertexEquiv N) (.inl v))⟩ : AnySignature K)=
      ⟨N.shape.arity v.1,N.vertex v.1⟩ := by
  change (⟨(finite N).arity ((Fintype.equivFin (Vertices N)).symm ((Fintype.equivFin (Vertices N)) (.inl v))),
    (finite N).vertex ((Fintype.equivFin (Vertices N)).symm ((Fintype.equivFin (Vertices N)) (.inl v)))⟩ : AnySignature K)=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- Each split occurrence is replaced by precisely two literal I labels. -/
theorem replacement_label (N : Network K n) (t : Split N) (b : Bool) :
    (⟨(expand N).shape.arity ((vertexEquiv N) (.inr (t,b))),
      (expand N).vertex ((vertexEquiv N) (.inr (t,b)))⟩ : AnySignature K)=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  change (⟨(finite N).arity ((Fintype.equivFin (Vertices N)).symm ((Fintype.equivFin (Vertices N)) (.inr (t,b)))),
    (finite N).vertex ((Fintype.equivFin (Vertices N)).symm ((Fintype.equivFin (Vertices N)) (.inr (t,b))))⟩ : AnySignature K)=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- An old edge keeps its exact oriented kernel, without changing its identity. -/
theorem old_edge_label (N : Network K n) (e : Fin N.shape.edges) :
    (expand N).edge ((edgeEquiv N) (.inl e))=N.edge e := by
  simp [edgeEquiv,expand,FiniteNetwork.toNetwork]
  rfl

/-- Nullary vertices cannot be split by the binary-X test. -/
theorem nullary_is_kept (N : Network K n) (v : Fin N.shape.vertices)
    (hv : N.shape.arity v=0) : ¬IsX N v := by
  intro hx
  have ha : N.shape.arity v=2 := congrArg Sigma.fst hx
  omega

end
end Holant.ReedMuller.TwoChart.NativeXExpansion
