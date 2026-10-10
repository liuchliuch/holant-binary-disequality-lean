import Holant.NetworkGluing
import Holant.NetworkAlgebra
import Holant.Proofs.Reductions.GeneralExtraction.NamedContraction


noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPartialJoin
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} {k : ℕ}

/-- Boundary slots 0,1 are retained; slots 2,...,k+1 are joined. -/
def block (k : ℕ) : Fin (k+2) ≃ (Fin 2 ⊕ Fin k) :=
  (finCongr (Nat.add_comm k 2)).trans finSumFinEquiv.symm

def word (u : Fin 2 → Bool) (z : Fin k → Bool) : Fin (k+2) → Bool :=
  fun i => Sum.elim u z (block k i)

def left (w : Fin 4 → Bool) : Fin 2 → Bool := fun i => w (Fin.castAdd 2 i)
def right (w : Fin 4 → Bool) : Fin 2 → Bool := fun i => w (Fin.natAdd 2 i)

abbrev Edges (L R : Network K (k+2)) :=
  (Fin L.shape.edges ⊕ Fin R.shape.edges) ⊕ Fin k

def ports (EL ER : Type*) (k : ℕ) :
    ((Fin (k+2) ⊕ (EL × Bool)) ⊕ (Fin (k+2) ⊕ (ER × Bool))) ≃
      (Fin 4 ⊕ ((((EL ⊕ ER) ⊕ Fin k) × Bool))) :=
  (Equiv.sumCongr (Equiv.sumCongr (block k) (Equiv.refl _))
    (Equiv.sumCongr (block k) (Equiv.refl _))).trans {
      toFun
        | .inl (.inl (.inl i)) => .inl (Fin.castAdd 2 i)
        | .inr (.inl (.inl i)) => .inl (Fin.natAdd 2 i)
        | .inl (.inl (.inr i)) => .inr (.inr i,false)
        | .inr (.inl (.inr i)) => .inr (.inr i,true)
        | .inl (.inr (e,b)) => .inr (.inl (.inl e),b)
        | .inr (.inr (e,b)) => .inr (.inl (.inr e),b)
      invFun
        | .inl i => match (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm i with
          | .inl j => .inl (.inl (.inl j))
          | .inr j => .inr (.inl (.inl j))
        | .inr (.inr i,false) => .inl (.inl (.inr i))
        | .inr (.inr i,true) => .inr (.inl (.inr i))
        | .inr (.inl (.inl e),b) => .inl (.inr (e,b))
        | .inr (.inl (.inr e),b) => .inr (.inr (e,b))
      left_inv := by
        rintro (((i | i) | ⟨e,b⟩) | ((i | i) | ⟨e,b⟩))
        all_goals first | rfl | (fin_cases i <;> rfl)
      right_inv := by
        rintro (i | ⟨((e | e) | i),b⟩)
        · fin_cases i <;> rfl
        · cases b <;> rfl
        · cases b <;> rfl
        · cases b <;> rfl }

def finite (L R : Network K (k+2)) (W : Fin k → Kernel K) :
    FiniteNetwork K (Fin L.shape.vertices ⊕ Fin R.shape.vertices) (Edges L R) 4 where
  arity := Sum.elim L.shape.arity R.shape.arity
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports R.shape.ports).trans (ports _ _ k))
  vertex
    | .inl v => L.vertex v
    | .inr v => R.vertex v
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e
    | .inr i => W i

def network (L R : Network K (k+2)) (W : Fin k → Kernel K) : Network K 4 :=
  (finite L R W).toNetwork

@[simp] theorem vertices (L R : Network K (k+2)) (W : Fin k → Kernel K) :
    (network L R W).shape.vertices=L.shape.vertices+R.shape.vertices := by
  simp [network,FiniteNetwork.toNetwork]
@[simp] theorem edges (L R : Network K (k+2)) (W : Fin k → Kernel K) :
    (network L R W).shape.edges=L.shape.edges+R.shape.edges+k := by
  simp [network,FiniteNetwork.toNetwork,Edges]

def assignments (L R : Network K (k+2)) :
    ((Edges L R × Bool) → Bool) ≃
      ((Fin k → Bool) × ((Fin k → Bool) ×
        (((Fin L.shape.edges × Bool) → Bool) × ((Fin R.shape.edges × Bool) → Bool)))) where
  toFun z := (fun i => z (.inr i,false),fun i => z (.inr i,true),
    fun q => z (.inl (.inl q.1),q.2),fun q => z (.inl (.inr q.1),q.2))
  invFun p q := match q with
    | (.inr i,false) => p.1 i
    | (.inr i,true) => p.2.1 i
    | (.inl (.inl e),b) => p.2.2.1 (e,b)
    | (.inl (.inr e),b) => p.2.2.2 (e,b)
  left_inv := by
    intro z; funext q
    rcases q with ⟨((e | e) | i),b⟩ <;> cases b <;> rfl
  right_inv := by intro p; rfl

variable [CommSemiring K]

def value (W : Fin k → Kernel K) (f g : Signature K (k+2)) : Signature K 4 :=
  fun w => ∑ x : Fin k → Bool, ∑ y : Fin k → Bool,
    f (word (left w) x) * g (word (right w) y) * ∏ i,W i (x i) (y i)

/-- Fubini for the actual graph, including the retained loops inside both
copies. Boundary values are the four exposed bits, not new vertex tables. -/
theorem denote (L R : Network K (k+2)) (W : Fin k → Kernel K) :
    (network L R W).denote=value W L.denote R.denote := by
  classical
  let : DecidableEq (Edges L R) := Classical.decEq _
  funext w
  rw [network,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote value
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
      Sum.elim w ((assignments L R).symm (x,y,zL,zR))
        ((finite L R W).ports ⟨.inl v,i⟩))=
      L.shape.assignment (word (left w) x) zL := by
    funext v i
    dsimp [finite,NetworkShape.assignment]
    change Sum.elim w _ (ports _ _ k (.inl (L.shape.ports ⟨v,i⟩)))=_
    cases hp : L.shape.ports ⟨v,i⟩ with
    | inr q => rfl
    | inl p =>
      change Sum.elim w _ (ports _ _ k (.inl (.inl p)))=word (left w) x p
      cases hb : block k p <;> simp [ports,word,Equiv.trans_apply,hb,left,assignments]
  have hr : (fun (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v)) =>
      Sum.elim w ((assignments L R).symm (x,y,zL,zR))
        ((finite L R W).ports ⟨.inr v,i⟩))=
      R.shape.assignment (word (right w) y) zR := by
    funext v i
    dsimp [finite,NetworkShape.assignment]
    change Sum.elim w _ (ports _ _ k (.inr (R.shape.ports ⟨v,i⟩)))=_
    cases hp : R.shape.ports ⟨v,i⟩ with
    | inr q => rfl
    | inl p =>
      change Sum.elim w _ (ports _ _ k (.inr (.inl p)))=word (right w) y p
      cases hb : block k p <;> simp [ports,word,Equiv.trans_apply,hb,right,assignments]
  dsimp [finite,assignments] at hl hr ⊢
  simp only [congrFun₂ hl,congrFun₂ hr]
  ac_rfl

theorem value_add_left (W : Fin k → Kernel K) (f₁ f₂ g : Signature K (k+2)) :
    value W (f₁+f₂) g=value W f₁ g+value W f₂ g := by
  funext w
  simp [value,add_mul,Finset.sum_add_distrib]
theorem value_add_right (W : Fin k → Kernel K) (f g₁ g₂ : Signature K (k+2)) :
    value W f (g₁+g₂)=value W f g₁+value W f g₂ := by
  funext w
  simp [value,mul_add,add_mul,Finset.sum_add_distrib]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPartialJoin
