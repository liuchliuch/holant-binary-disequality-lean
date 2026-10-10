import Holant.NetworkGluing
import Holant.ReedMuller.RadonAccess.ProgramNetwork

/-! Partial gluing of actual ordinary-boundary networks.  The first block of
right boundary ports is consumed and the second block survives in its original
order. Every old vertex, local port, edge and scalar component is retained. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.RadonAccess
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {K : Type*} {n m : ℕ}

abbrev StitchEdges (L : Network K n) (R : Network K (n+m)) :=
  (Fin L.shape.edges ⊕ Fin R.shape.edges) ⊕ Fin n

def stitchPorts (EL ER : Type*) (n m : ℕ) :
    ((Fin n ⊕ (EL × Bool)) ⊕ ((Fin n ⊕ Fin m) ⊕ (ER × Bool))) ≃
      (Fin m ⊕ (((EL ⊕ ER) ⊕ Fin n) × Bool)) where
  toFun
    | .inl (.inl i) => .inr (.inr i,false)
    | .inr (.inl (.inl i)) => .inr (.inr i,true)
    | .inr (.inl (.inr i)) => .inl i
    | .inl (.inr (e,b)) => .inr (.inl (.inl e),b)
    | .inr (.inr (e,b)) => .inr (.inl (.inr e),b)
  invFun
    | .inr (.inr i,false) => .inl (.inl i)
    | .inr (.inr i,true) => .inr (.inl (.inl i))
    | .inl i => .inr (.inl (.inr i))
    | .inr (.inl (.inl e),b) => .inl (.inr (e,b))
    | .inr (.inl (.inr e),b) => .inr (.inr (e,b))
  left_inv := by rintro ((i|⟨e,b⟩)|((i|i)|⟨e,b⟩)) <;> rfl
  right_inv := by
    rintro (i|⟨((e|e)|i),b⟩)
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

def stitchFinite (L : Network K n) (R : Network K (n+m)) (W : Fin n → Kernel K) :
    FiniteNetwork K (Fin L.shape.vertices ⊕ Fin R.shape.vertices) (StitchEdges L R) m where
  arity := Sum.elim L.shape.arity R.shape.arity
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports
      (R.shape.ports.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))).trans
        (stitchPorts _ _ n m))
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e
    | .inr i => W i

def stitch (L : Network K n) (R : Network K (n+m)) (W : Fin n → Kernel K) : Network K m :=
  (stitchFinite L R W).toNetwork

@[simp] theorem stitch_vertices (L : Network K n) (R : Network K (n+m)) (W : Fin n → Kernel K) :
    (stitch L R W).shape.vertices=L.shape.vertices+R.shape.vertices := by
  simp [stitch,FiniteNetwork.toNetwork]
@[simp] theorem stitch_edges (L : Network K n) (R : Network K (n+m)) (W : Fin n → Kernel K) :
    (stitch L R W).shape.edges=L.shape.edges+R.shape.edges+n := by
  simp [stitch,FiniteNetwork.toNetwork,StitchEdges]

def stitchAssignments (L : Network K n) (R : Network K (n+m)) :
    ((StitchEdges L R × Bool) → Bool) ≃
      ((Fin n → Bool) × ((Fin n → Bool) ×
        (((Fin L.shape.edges × Bool) → Bool) × ((Fin R.shape.edges × Bool) → Bool)))) where
  toFun := fun z => (fun i => z (.inr i,false),fun i => z (.inr i,true),
    fun q => z (.inl (.inl q.1),q.2),fun q => z (.inl (.inr q.1),q.2))
  invFun := fun p q => match q with
    | (.inr i,false) => p.1 i
    | (.inr i,true) => p.2.1 i
    | (.inl (.inl e),b) => p.2.2.1 (e,b)
    | (.inl (.inr e),b) => p.2.2.2 (e,b)
  left_inv := by intro z;funext q;rcases q with ⟨((e|e)|i),b⟩ <;> cases b <;> rfl
  right_inv := fun _ => rfl

set_option maxHeartbeats 600000 in
theorem denote_stitch [CommSemiring K] (L : Network K n) (R : Network K (n+m))
    (W : Fin n → Kernel K) (b : Fin m → Bool) :
    (stitch L R W).denote b=
      ∑ x : Fin n → Bool,∑ y : Fin n → Bool,
        L.denote x*R.denote (Fin.addCases y b)*∏ i,W i (x i) (y i) := by
  let : DecidableEq (StitchEdges L R) := Classical.decEq _
  rw [stitch,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : (StitchEdges L R × Bool) → Bool,
    (∏ v,(stitchFinite L R W).vertex v (fun i => Sum.elim b z ((stitchFinite L R W).ports ⟨v,i⟩)))*
    ∏ e,(stitchFinite L R W).edge e (z (e,false)) (z (e,true)))=_
  rw [←(stitchAssignments L R).symm.sum_comp]
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
  dsimp only [stitchFinite]
  simp only [Fintype.prod_sum_type]
  have hl (v : Fin L.shape.vertices) :
      (fun i => Sum.elim b ((stitchAssignments L R).symm (x,y,zL,zR))
        ((stitchFinite L R W).ports ⟨.inl v,i⟩))=L.shape.assignment x zL v := by
    funext i
    dsimp [stitchFinite,NetworkShape.assignment]
    change Sum.elim b ((stitchAssignments L R).symm (x,y,zL,zR))
      (stitchPorts _ _ n m (.inl (L.shape.ports ⟨v,i⟩)))=_
    cases L.shape.ports ⟨v,i⟩ <;> rfl
  have hr (v : Fin R.shape.vertices) :
      (fun i => Sum.elim b ((stitchAssignments L R).symm (x,y,zL,zR))
        ((stitchFinite L R W).ports ⟨.inr v,i⟩))=R.shape.assignment (Fin.addCases y b) zR v := by
    funext i
    dsimp [stitchFinite,NetworkShape.assignment]
    change Sum.elim b ((stitchAssignments L R).symm (x,y,zL,zR))
      (stitchPorts _ _ n m (.inr ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))
        (R.shape.ports ⟨v,i⟩))))=_
    cases hp : R.shape.ports ⟨v,i⟩ with
    | inr e => rfl
    | inl j =>
      obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
      cases j <;> simp [stitchPorts,stitchAssignments]
  dsimp [stitchAssignments]
  dsimp [stitchFinite,stitchAssignments] at hl hr
  simp only [hl,hr]
  ac_rfl

theorem prod_native {ι : Type*} [Fintype ι] (a b : ι → Bool) :
    (∏ i,(Signature.disequality (a i) (b i) : ℂ))=
      if b=(fun i => !(a i)) then 1 else 0 := by
  simp only [Signature.disequality,Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h;funext i;exact Bool.eq_not_iff.mpr (Ne.symm (h i))
  · intro h i;exact Ne.symm (Bool.eq_not_iff.mp (congrFun h i))

theorem denote_stitch_native (L : Network ℂ n) (R : Network ℂ (n+m)) (b : Fin m → Bool) :
    (stitch L R (fun _ => Signature.disequality)).denote b=
      ∑ x : Fin n → Bool,L.denote x*R.denote (Fin.addCases (fun i => !(x i)) b) := by
  rw [denote_stitch]
  simp only [prod_native,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem stitch_uses (F : SignatureFamily ℂ) (L : Network ℂ n) (R : Network ℂ (n+m))
    (W : Fin n → Kernel ℂ) (hL : Uses F L) (hR : Uses F R) : Uses F (stitch L R W) := by
  intro v
  change (⟨_,(stitchFinite L R W).vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature ℂ)∈F
  cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem stitch_native (L : Network ℂ n) (R : Network ℂ (n+m))
    (hL : ∀ e,L.edge e=Signature.disequality) (hR : ∀ e,R.edge e=Signature.disequality) :
    ∀ e,(stitch L R (fun _ => Signature.disequality)).edge e=Signature.disequality := by
  intro e
  change (stitchFinite L R (fun _ => Signature.disequality)).edge
    ((Fintype.equivFin (StitchEdges L R)).symm e)=_
  cases (Fintype.equivFin (StitchEdges L R)).symm e with
  | inr i => rfl
  | inl e => cases e with
    | inl e => exact hL e
    | inr e => exact hR e

/-- Exact incidence certificates: the left port and the first right block
become the false/true ends of their new native edge, with no local relabeling. -/
theorem stitch_left_boundary (L : Network K n) (R : Network K (n+m))
    (W : Fin n → Kernel K) (v : Fin L.shape.vertices) (i : Fin (L.shape.arity v))
    (j : Fin n) (hp : L.shape.ports ⟨v,i⟩=.inl j) :
    (stitchFinite L R W).ports ⟨.inl v,i⟩=.inr (.inr j,false) := by
  change stitchPorts _ _ n m (.inl (L.shape.ports ⟨v,i⟩))=_
  rw [hp]
  rfl

theorem stitch_right_joined (L : Network K n) (R : Network K (n+m))
    (W : Fin n → Kernel K) (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v))
    (j : Fin n) (hp : R.shape.ports ⟨v,i⟩=.inl (Fin.castAdd m j)) :
    (stitchFinite L R W).ports ⟨.inr v,i⟩=.inr (.inr j,true) := by
  change stitchPorts _ _ n m (.inr ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))
    (R.shape.ports ⟨v,i⟩)))=_
  rw [hp]
  simp [stitchPorts]

theorem stitch_right_surviving (L : Network K n) (R : Network K (n+m))
    (W : Fin n → Kernel K) (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v))
    (j : Fin m) (hp : R.shape.ports ⟨v,i⟩=.inl (Fin.natAdd n j)) :
    (stitchFinite L R W).ports ⟨.inr v,i⟩=.inl j := by
  change stitchPorts _ _ n m (.inr ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))
    (R.shape.ports ⟨v,i⟩)))=_
  rw [hp]
  simp [stitchPorts]

end
end Holant.ReedMuller.SignedRadon
