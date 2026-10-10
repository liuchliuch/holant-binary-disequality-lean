import Holant.ReedMuller.SignedRadon.Graph
import Holant.ReedMuller.SignedRadon.Stitch

/-! The original g corolla is connected to the fixed actual graph input block
through native X edges. This is graph composition, not signature replacement. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem vector_not (x : Fin n → Bool) : vectorWord (fun i => !(x i))=vectorWord x+ones n := by
  funext i
  change boolEquiv (!(x i))=boolEquiv (x i)+1
  cases x i <;> decide

def graphApply {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) : Network ℂ n :=
  stitch (Network.corolla g) Γ.network (fun _ => Signature.disequality)

def inputLift (A : OrthogonalMap n) (z : Fin n → Bool) : BinaryVector n :=
  A.symm (vectorWord z)+ones n

theorem graph_input_unique (A : OrthogonalMap n) (x z : Fin n → Bool) :
    vectorWord z=A (vectorWord (fun i => !(x i))) ↔ x=wordVector (inputLift A z) := by
  rw [vector_not,A.map_add,A.fixes_ones]
  constructor
  · intro h
    apply (Equiv.piCongrRight (fun _ : Fin n => boolEquiv)).injective
    change vectorWord x=vectorWord (wordVector (inputLift A z))
    rw [vector_word]
    have hh := congrArg A.symm h
    rw [A.symm.map_add,A.symm_apply_apply,A.symm.fixes_ones] at hh
    unfold inputLift
    rw [hh,add_assoc,binary_add_self,add_zero]
  · intro h
    rw [h,vector_word,inputLift,A.map_add,A.apply_symm_apply,A.fixes_ones,
      add_assoc,binary_add_self,add_zero]

theorem graphApply_denote {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) (z : Fin n → Bool) :
    (graphApply Γ g).denote z=Γ.scalar*g (wordVector (inputLift A z)) := by
  rw [graphApply,denote_stitch_native]
  simp only [Network.denote_corolla,Γ.denote,Pi.smul_apply,smul_eq_mul,graphSignature]
  have hs (x : Fin n → Bool) :
      vectorWord (Fin.addCases (fun i => !(x i)) z)=
        joinVector (vectorWord (fun i => !(x i))) (vectorWord z) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [vectorWord,joinVector,Fin.addCases_left,Fin.addCases_right]
  simp only [hs,left_join,right_join,graph_input_unique,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

def cardFamily (κ : ZMod 2 → ZMod 2 → ℂ) (g : Signature ℂ n) : SignatureFamily ℂ :=
  {f | f=⟨n,g⟩ ∨ f∈retainedFamily κ}

theorem graphApply_uses {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) : Uses (cardFamily κ g) (graphApply Γ g) :=
  stitch_uses _ _ _ _ (fun _ => Or.inl rfl) (fun v => Or.inr (Γ.uses v))

theorem graphApply_native {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) :
    ∀ e,(graphApply Γ g).edge e=Signature.disequality :=
  stitch_native _ _ (fun e => Fin.elim0 e) Γ.native

@[simp] theorem graphApply_vertices {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) :
    (graphApply Γ g).shape.vertices=1+Γ.network.shape.vertices := by
  simp [graphApply,Network.corolla]
@[simp] theorem graphApply_edges {κ : ZMod 2 → ZMod 2 → ℂ} {A : OrthogonalMap n}
    (Γ : ActualGraph κ A) (g : Signature ℂ n) :
    (graphApply Γ g).shape.edges=Γ.network.shape.edges+n := by
  simp [graphApply,Network.corolla]

end
end Holant.ReedMuller.SignedRadon
