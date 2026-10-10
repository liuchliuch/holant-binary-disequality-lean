import Holant.OneHot.Decomposition.ForestAssembly

/-! Exact endpoint identities when ordered child trees are assembled. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Forest

variable {K : Type*}

/-- An assembled edge is either one incoming child edge or an internal edge of
exactly one child tree; multiplicities are retained by an explicit equivalence. -/
def ofFnEdge : {n : ℕ} → (b : Fin n → K) → (ts : Fin n → Tree K) →
    (ofFn b ts).Edge ≃ (Σ i, Unit ⊕ (ts i).Edge)
  | 0, _, _ => {
      toFun := Empty.elim
      invFun := fun p => Fin.elim0 p.1
      left_inv := fun p => Empty.elim p
      right_inv := fun p => Fin.elim0 p.1 }
  | n + 1, b, ts =>
      (Equiv.sumAssoc Unit (ts 0).Edge _).symm.trans
        ((Equiv.sumCongr (Equiv.refl _) (ofFnEdge (fun i : Fin n => b i.succ)
          (fun i : Fin n => ts i.succ))).trans
            (Decomposition.sigmaFinSucc (fun i => Unit ⊕ (ts i).Edge)).symm)

/-- Forget the port number but retain whether an endpoint is at the common root
or at an actual descendant vertex. -/
def endpointVertex (ts : Forest K) (e : ts.Edge) (b : Bool) : Unit ⊕ ts.Vertex :=
  Sum.map (fun _ => ()) (fun p => p.1) (ts.portInv (e, b))

@[simp] theorem endpointVertex_cons_head (b : K) (t : Tree K) (ts : Forest K) (z : Bool) :
    (Forest.cons b t ts).endpointVertex (.inl ()) z =
      if z then .inl () else .inr (.inl (t.portInv (.inl 0)).1) := by
  cases z <;> rfl

@[simp] theorem endpointVertex_cons_tree (b : K) (t : Tree K) (ts : Forest K)
    (e : t.Edge) (z : Bool) :
    (Forest.cons b t ts).endpointVertex (.inr (.inl e)) z =
      .inr (.inl (t.portInv (.inr (e, z))).1) := rfl

@[simp] theorem endpointVertex_cons_tail (b : K) (t : Tree K) (ts : Forest K)
    (e : ts.Edge) (z : Bool) :
    (Forest.cons b t ts).endpointVertex (.inr (.inr e)) z =
      Sum.map id Sum.inr (ts.endpointVertex e z) := by
  unfold endpointVertex
  simp only [Forest.portInv]
  cases ts.portInv (e, z) <;> rfl

/-- Assembly preserves both occurrences of each edge, including the attaching
edge's child/root orientation and every endpoint internal to the child tree. -/
theorem endpointVertex_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (e : (ofFn b ts).Edge) (z : Bool) :
    Sum.map id (ofFnVertex b ts) ((ofFn b ts).endpointVertex e z) =
      match (ofFnEdge b ts) e with
      | ⟨i, .inl _⟩ => if z then .inl () else .inr ⟨i, ((ts i).portInv (.inl 0)).1⟩
      | ⟨i, .inr f⟩ => .inr ⟨i, ((ts i).portInv (.inr (f, z))).1⟩ := by
  induction n with
  | zero => exact Empty.elim e
  | succ n ih =>
    rcases e with u | e | e
    · cases u
      cases z <;> rfl
    · rfl
    · have h := ih (fun i => b i.succ) (fun i => ts i.succ) e
      let lift : (Unit ⊕ Σ i : Fin n, (ts i.succ).Vertex) →
          (Unit ⊕ Σ i : Fin (n + 1), (ts i).Vertex) :=
        Sum.map id (fun p => ⟨p.1.succ, p.2⟩)
      have hm : Sum.map id (ofFnVertex b ts)
          ((ofFn b ts).endpointVertex (.inr (.inr e)) z) =
          lift (Sum.map id (ofFnVertex (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ))
            ((ofFn (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ)).endpointVertex e z)) := by
        unfold endpointVertex
        cases hp : (ofFn (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ)).portInv (e, z) with
        | inl j => simp [ofFn, Forest.portInv, hp, lift, ofFnVertex, Decomposition.sigmaFinSucc]
        | inr p =>
          simp only [ofFn, Forest.portInv, hp, lift, ofFnVertex, Decomposition.sigmaFinSucc,
            Equiv.trans_apply, Sum.map_inr]
          cases hq : (ofFnVertex (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ)) p.1
          simp [Equiv.sumCongr, hq]
      refine hm.trans ((congrArg lift h).trans ?_)
      simp only [ofFnEdge, Equiv.trans_apply, Equiv.sumCongr_apply]
      generalize he : ofFnEdge (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ) e = q
      rcases q with ⟨i, u | f⟩
      · cases z <;> simp [lift, Equiv.sumAssoc, Decomposition.sigmaFinSucc, he]
      · simp [lift, Equiv.sumAssoc, Decomposition.sigmaFinSucc, he]

/-- Singleton weight on a forest root slot or an actual descendant port. -/
def slotCoefficient (ts : Forest K) : (Fin ts.length ⊕ ts.Occurrence) → K
  | .inl i => ts.coefficients i
  | .inr p => ts.portCoefficient p.1 p.2

/-- Adding earlier siblings changes no coefficient on the remaining forest. -/
theorem slotCoefficient_cons_tail (b : K) (t : Tree K) (ts : Forest K)
    (e : ts.Edge) (z : Bool) :
    (Forest.cons b t ts).slotCoefficient ((Forest.cons b t ts).portInv (.inr (.inr e), z)) =
      ts.slotCoefficient (ts.portInv (e, z)) := by
  simp only [Forest.portInv]
  cases ts.portInv (e, z) <;> rfl

/-- The true endpoint keeps the child-edge coefficient at its original parent. -/
theorem slotCoefficient_ofFn_true {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (e : (ofFn b ts).Edge) :
    (ofFn b ts).slotCoefficient ((ofFn b ts).portInv (e, true)) =
      match (ofFnEdge b ts) e with
      | ⟨i, .inl _⟩ => b i
      | ⟨i, .inr g⟩ => (ts i).portCoefficient ((ts i).portInv (.inr (g, true))).1
          ((ts i).portInv (.inr (g, true))).2 := by
  induction n with
  | zero => exact Empty.elim e
  | succ n ih =>
    rcases e with u | e | e
    · cases u; rfl
    · rfl
    · refine (slotCoefficient_cons_tail (b 0) (ts 0)
        (ofFn (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ)) e true).trans ?_
      refine (ih (fun i => b i.succ) (fun i => ts i.succ) e).trans ?_
      simp only [ofFnEdge, Equiv.trans_apply, Equiv.sumCongr_apply]
      generalize he : ofFnEdge (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ) e = q
      rcases q with ⟨i, u | g⟩ <;>
        simp [Equiv.sumAssoc, Decomposition.sigmaFinSucc, he]

end Holant.OneHot.Forest

namespace Holant.OneHot.Tree

variable {K : Type*}

/-- Coefficients at both actual internal ends agree with their forest slots. -/
theorem portCoefficient_node_endpoint (a b : K) (ts : Forest K) (e : ts.Edge) (z : Bool) :
    (Tree.node a b ts).portCoefficient ((Tree.node a b ts).portInv (.inr (e, z))).1
      ((Tree.node a b ts).portInv (.inr (e, z))).2 =
      ts.slotCoefficient (ts.portInv (e, z)) := by
  simp only [Tree.portInv]
  cases ts.portInv (e, z) <;> rfl

end Holant.OneHot.Tree
