import Holant.ReedMuller.RadonAccess.ProgramNetwork
import Holant.ReedMuller.RadonAccess.Directions
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! Close two chosen output coordinates of an actual one-copy circuit. Its
boundary is the literal two-lift Radon sum; the residual order is recorded. -/
namespace Holant.ReedMuller.RadonAccess
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork GenerationNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def pairNetwork (p : GenerationProgram (n+2)) (g : Signature ℂ (n+2))
    (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2) : Network ℂ n :=
  (reindex (oneCopy p g) order.symm).contract (parityKernel epsilon)

def orderedVector (order : Equiv.Perm (Fin (n+2))) (a b : ZMod 2)
    (w : BinaryVector n) : BinaryVector (n+2) :=
  fun i => (Fin.cons a (Fin.cons b w) : Fin (n+2) → ZMod 2) (order.symm i)

theorem vector_orderedBool (order : Equiv.Perm (Fin (n+2))) (a b : Bool) (x : Fin n → Bool) :
    vectorWord (fun i => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) (order.symm i))=
      orderedVector order (boolEquiv a) (boolEquiv b) (vectorWord x) := by
  funext i
  change boolEquiv ((Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) (order.symm i))=
    (Fin.cons (boolEquiv a) (Fin.cons (boolEquiv b) (vectorWord x)) : Fin (n+2) → ZMod 2) (order.symm i)
  generalize hi : order.symm i=j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j <;> rfl

theorem orderedVector_add (order : Equiv.Perm (Fin (n+2))) (a b c d : ZMod 2)
    (w z : BinaryVector n) :
    orderedVector order (a+c) (b+d) (w+z)=orderedVector order a b w+orderedVector order c d z := by
  funext i
  change (Fin.cons (a+c) (Fin.cons (b+d) (w+z)) : Fin (n+2) → ZMod 2) (order.symm i)=
    (Fin.cons a (Fin.cons b w) : Fin (n+2) → ZMod 2) (order.symm i)+
    (Fin.cons c (Fin.cons d z) : Fin (n+2) → ZMod 2) (order.symm i)
  generalize hi : order.symm i=j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j <;> rfl

theorem word_add (p : GenerationProgram n) (x y : BinaryVector n) :
    p.word (x+y)=p.word x+p.word y := by
  simpa only [GenerationProgram.linear_apply] using p.linear.map_add x y

def pairDirection (p : GenerationProgram (n+2)) (order : Equiv.Perm (Fin (n+2))) :
    BinaryVector (n+2) := p.inverse.word (orderedVector order 1 1 0)

def pairBase (p : GenerationProgram (n+2)) (order : Equiv.Perm (Fin (n+2)))
    (epsilon : ZMod 2) (x : Fin n → Bool) : BinaryVector (n+2) :=
  p.inverse.word (orderedVector order epsilon 0 (vectorWord x))

def pairSum (p : GenerationProgram (n+2)) (order : Equiv.Perm (Fin (n+2)))
    (epsilon : ZMod 2) (g : Signature ℂ (n+2)) : Signature ℂ n := fun x =>
  g (wordVector (pairBase p order epsilon x))+
    g (wordVector (pairBase p order epsilon x+pairDirection p order))

/-- There are exactly the two original-input evaluations in the requested
translation orbit, with coefficient one on each. -/
theorem pairNetwork_denote (p : GenerationProgram (n+2)) (g : Signature ℂ (n+2))
    (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2) :
    (pairNetwork p g order epsilon).denote=pairSum p order epsilon g := by
  funext x
  rw [pairNetwork,Network.denote_contract,denote_reindex]
  simp only [Signature.contract,Tensor.reindex,oneCopy_denote,vector_orderedBool]
  have h00 : orderedVector order 0 0 (vectorWord x)+orderedVector order 1 1 0=
      orderedVector order 1 1 (vectorWord x) := by
    rw [←orderedVector_add]
    simp
  have h10 : orderedVector order 1 0 (vectorWord x)+orderedVector order 1 1 0=
      orderedVector order 0 1 (vectorWord x) := by
    rw [←orderedVector_add]
    have htwo : (1 : ZMod 2)+1=0 := by decide
    simp [htwo]
  unfold pairSum pairBase pairDirection
  rw [←word_add]
  have hep : epsilon=0 ∨ epsilon=1 := (by decide : ∀ e : ZMod 2,e=0 ∨ e=1) epsilon
  rcases hep with rfl | rfl
  · rw [h00]
    simp [parityKernel_zero,Signature.equality,Fintype.sum_bool,boolEquiv,add_comm]
  · rw [h10]
    simp [parityKernel_one,Signature.disequality,Fintype.sum_bool,boolEquiv,add_comm]

theorem pairNetwork_uses (F : SignatureFamily ℂ) (p : GenerationProgram (n+2))
    (g : Signature ℂ (n+2)) (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2)
    (hg : (⟨n+2,g⟩ : AnySignature ℂ)∈F) (hRM : (⟨8,rmCore⟩ : AnySignature ℂ)∈F) :
    Uses F (pairNetwork p g order epsilon) := oneCopy_uses F p g hg hRM

theorem pairNetwork_edges (p : GenerationProgram (n+2)) (g : Signature ℂ (n+2))
    (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2) : EdgesIX (pairNetwork p g order epsilon) := by
  intro e
  refine Fin.cases ?_ (fun j => ?_) e
  · change parityKernel epsilon=Signature.equality ∨ parityKernel epsilon=Signature.disequality
    fin_cases epsilon
    · exact Or.inl parityKernel_zero
    · exact Or.inr parityKernel_one
  · exact oneCopy_edges p g j

theorem pairNetwork_vertices (p : GenerationProgram (n+2)) (g : Signature ℂ (n+2))
    (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2) :
    (pairNetwork p g order epsilon).shape.vertices≤1+p.length := oneCopy_vertices p g

theorem pairNetwork_edge_bound (p : GenerationProgram (n+2)) (g : Signature ℂ (n+2))
    (order : Equiv.Perm (Fin (n+2))) (epsilon : ZMod 2) :
    (pairNetwork p g order epsilon).shape.edges≤4*p.length+1 := by
  change (oneCopy p g).shape.edges+1≤4*p.length+1
  exact Nat.add_le_add_right (oneCopy_edge_bound p g) 1

end
end Holant.ReedMuller.RadonAccess
