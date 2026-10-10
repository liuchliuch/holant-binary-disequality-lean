import Holant.ReedMuller.TwoChart.NetworkPlug
import Holant.ReedMuller.TwoChart.Relation
import Holant.NetworkAlgebra

/-! The actual retained RM/Bell networks have algebraic coefficients. Lifting
keeps their incidence, every vertex and edge, and the complete finite sum. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem sign_algebraic (b : ZMod 2) : sign b∈AlgebraicComplex := by
  rcases TwoTranslate.binary_cases b with rfl|rfl
  · simpa using (AlgebraicComplex.one_mem)
  · simpa using (AlgebraicComplex.neg_mem AlgebraicComplex.one_mem)

 theorem parityKernel_algebraic (d : ZMod 2) (a b : Bool) : parityKernel d a b∈AlgebraicComplex := by
  unfold parityKernel
  split_ifs
  · exact AlgebraicComplex.one_mem
  · exact AlgebraicComplex.zero_mem

 theorem bell_algebraic (d l : ZMod 2) (x : Word 2) : bellSignature d l x∈AlgebraicComplex := by
  exact AlgebraicComplex.mul_mem (sign_algebraic _) (parityKernel_algebraic _ _ _)

 theorem rm_algebraic (x : Word 8) : rmCore x∈AlgebraicComplex := by
  unfold rmCore flatSignature
  split_ifs
  · exact AlgebraicComplex.one_mem
  · exact AlgebraicComplex.zero_mem

 theorem retained_algebraic (κ : ZMod 2→ZMod 2→AlgebraicComplex)
    (f : AnySignature ℂ) (hf : f∈retainedFamily (fun d l => (κ d l:ℂ))) :
    ∀ x,f.2 x∈AlgebraicComplex := by
  rcases hf with rfl|⟨d,l,rfl⟩
  · exact rm_algebraic
  · intro x
    exact AlgebraicComplex.mul_mem (κ d l).property (bell_algebraic d l x)

 def algebraicLift (N : Network ℂ n)
    (hv : ∀ v x,N.vertex v x∈AlgebraicComplex)
    (he : ∀ e a b,N.edge e a b∈AlgebraicComplex) : Network AlgebraicComplex n where
  shape := N.shape
  vertex := fun v x => ⟨N.vertex v x,hv v x⟩
  edge := fun e a b => ⟨N.edge e a b,he e a b⟩

 theorem algebraicLift_map (N : Network ℂ n)
    (hv : ∀ v x,N.vertex v x∈AlgebraicComplex)
    (he : ∀ e a b,N.edge e a b∈AlgebraicComplex) :
    (algebraicLift N hv he).map AlgebraicComplex.subtype=N := rfl

 theorem algebraicLift_denote (N : Network ℂ n)
    (hv : ∀ v x,N.vertex v x∈AlgebraicComplex)
    (he : ∀ e a b,N.edge e a b∈AlgebraicComplex) (x : Word n) :
    ((algebraicLift N hv he).denote x:ℂ)=N.denote x := by
  have H := Network.denote_map AlgebraicComplex.subtype (algebraicLift N hv he) x
  rw [algebraicLift_map] at H
  exact H.symm

 theorem native_edges_algebraic (N : Network ℂ n)
    (he : ∀e,N.edge e=Signature.disequality) : ∀ e a b,N.edge e a b∈AlgebraicComplex := by
  intro e a b
  rw [he]
  cases a <;> cases b <;> first | exact AlgebraicComplex.zero_mem | exact AlgebraicComplex.one_mem

 theorem actual_context_algebraic (κ : ZMod 2→ZMod 2→AlgebraicComplex)
    (N : Network ℂ n)
    (hv : ∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈retainedFamily (fun d l => (κ d l:ℂ)))
    (he : ∀e,N.edge e=Signature.disequality) :
    ∃ M : Network AlgebraicComplex n,M.shape=N.shape ∧
      M.map AlgebraicComplex.subtype=N ∧ ∀x,(M.denote x:ℂ)=N.denote x := by
  let hV := fun v => retained_algebraic κ ⟨N.shape.arity v,N.vertex v⟩ (hv v)
  let hE := native_edges_algebraic N he
  exact ⟨algebraicLift N hV hE,rfl,algebraicLift_map _ _ _,algebraicLift_denote _ _ _⟩

end
end Holant.ReedMuller.TwoChart
