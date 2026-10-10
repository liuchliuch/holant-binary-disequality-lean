import Holant.ReedMuller.SignedRadon.GraphApply
import Holant.ReedMuller.SignedRadon.Coordinates

/-! One original g occurrence, the chosen actual graph network, and one actual
ordered Bell occurrence. All n+2 added edges are literal native X edges. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork GenerationNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
open Holant.Dihedral.CompatibleClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def pairInputOrder (F : RadonAccess.RadonFrame (n+2)) : Fin (n+2) ≃ Fin (2+n) :=
  (pairOrder F.i F.j).symm.trans (finCongr (Nat.add_comm n 2))

def signedNetwork {κ : ZMod 2 → ZMod 2 → ℂ} (F : RadonAccess.RadonFrame (n+2))
    (Γ : ActualGraph κ F.A) (g : Signature ℂ (n+2)) (d l : ZMod 2) : Network ℂ n :=
  stitch (Network.corolla (κ d l • bellSignature d l))
    (reindex (graphApply Γ g) (pairInputOrder F)) (fun _ => Signature.disequality)

def twoBits : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun x := (x 0,x 1)
  invFun p := ![p.1,p.2]
  left_inv := by intro x;funext i;fin_cases i <;> rfl
  right_inv := fun _ => rfl

theorem pairInput_word (F : RadonAccess.RadonFrame (n+2)) (a b : Bool) (x : Fin n → Bool) :
    (fun i => Fin.addCases ![a,b] x (pairInputOrder F i))=
      fun i => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) ((pairOrder F.i F.j).symm i) := by
  funext i
  obtain ⟨j,rfl⟩ := (pairOrder F.i F.j).surjective i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) j
  · simp only [pairInputOrder,Equiv.trans_apply,Equiv.symm_apply_apply]
    change Fin.addCases ![a,b] x (Fin.castAdd n (0 : Fin 2))=a
    rw [Fin.addCases_left]
    rfl
  · simp only [pairInputOrder,Equiv.trans_apply,Equiv.symm_apply_apply]
    change Fin.addCases ![a,b] x (Fin.castAdd n (1 : Fin 2))=b
    rw [Fin.addCases_left]
    rfl
  · have hh : (finCongr (Nat.add_comm n 2)) j.succ.succ=Fin.natAdd 2 j := by
      apply Fin.ext
      simp
      omega
    simp only [pairInputOrder,Equiv.trans_apply,Equiv.symm_apply_apply,hh,Fin.addCases_right]
    rfl

theorem orderedVector_ones (F : RadonAccess.RadonFrame (n+2)) :
    orderedVector (pairOrder F.i F.j) 1 1 (ones n)=ones (n+2) := by
  funext i
  change (Fin.cons 1 (Fin.cons 1 (ones n)) : BinaryVector (n+2)) ((pairOrder F.i F.j).symm i)=1
  generalize (pairOrder F.i F.j).symm i=j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) j <;> rfl

def pairLift (F : RadonAccess.RadonFrame (n+2)) (a b : ZMod 2) (x : BinaryVector n) :
    BinaryVector (n+2) := F.A.symm (orderedVector (pairOrder F.i F.j) a b (x+ones n))

theorem inputLift_pair (F : RadonAccess.RadonFrame (n+2)) (a b : Bool) (x : Fin n → Bool) :
    inputLift F.A (fun i => Fin.addCases ![!a,!b] x (pairInputOrder F i))=
      pairLift F (boolEquiv a) (boolEquiv b) (vectorWord x) := by
  rw [pairInput_word,inputLift,vector_orderedBool]
  rw [←F.A.symm.fixes_ones,←F.A.symm.map_add,←orderedVector_ones F,←orderedVector_add]
  have hbit (a : Bool) : boolEquiv (!a)+1=boolEquiv a := by cases a <;> decide
  rw [hbit,hbit]
  rfl

theorem pairLift_zero (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2) (x : BinaryVector n) :
    pairLift F d 0 x=RadonFrame.boundaryLift F d x := by
  rw [pairLift,F.orderedVector_decomposition,zero_smul,add_zero,F.A.symm.map_add,F.A.symm.map_smul]
  rfl

theorem pairLift_translate (F : RadonAccess.RadonFrame (n+2)) (a b : ZMod 2) (x : BinaryVector n) :
    pairLift F (a+1) (b+1) x=pairLift F a b x+F.v := by
  have he : orderedVector (pairOrder F.i F.j) 1 1 (0 : BinaryVector n)=unitWord F.i+unitWord F.j := by
    rw [F.orderedVector_decomposition,one_smul,one_smul]
    have hz : F.extendRemaining (F.pairRemainingWord 0)=0 := by
      funext i
      simp [RadonAccess.RadonFrame.extendRemaining,RadonAccess.RadonFrame.pairRemainingWord]
    rw [hz,add_zero]
  unfold pairLift RadonAccess.RadonFrame.v
  rw [←F.A.symm.map_add,←he,←orderedVector_add,add_zero]

/-- The sum is over the actual ordered Bell inputs; complements from both
native output edges have already been accounted for by `inputLift_pair`. -/
theorem signedNetwork_denote_sum {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) (x : Fin n → Bool) :
    (signedNetwork F Γ g d l).denote x=
      (Γ.scalar*κ d l)*(∑ a : Bool,∑ b : Bool,
        bellKernel d l a b*g (wordVector (pairLift F (boolEquiv a) (boolEquiv b) (vectorWord x)))) := by
  rw [signedNetwork,denote_stitch_native]
  simp only [Network.denote_corolla,Pi.smul_apply,smul_eq_mul,denote_reindex,Tensor.reindex,
    graphApply_denote]
  rw [←twoBits.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hn (a b : Bool) : (fun i => !((twoBits.symm (a,b)) i))=![!a,!b] := by
    funext i
    fin_cases i <;> rfl
  simp only [hn,inputLift_pair]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (κ d l*bellKernel d l a b)*(Γ.scalar*g _)=_
  ring

/-- Exactly two lifts survive on each layer, with their correct exterior and
relative signs. No multiplicity or zero realization scalar is discarded. -/
theorem signedNetwork_denote {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    (signedNetwork F Γ g d l).denote=(Γ.scalar*κ d l) • RadonFrame.boundaryCard F d l g := by
  funext x
  rw [signedNetwork_denote_sum,Pi.smul_apply,smul_eq_mul]
  congr 1
  rw [RadonFrame.boundaryCard_apply]
  have h00 := pairLift_zero F 0 (vectorWord x)
  have h10 := pairLift_zero F 1 (vectorWord x)
  have h11 := pairLift_translate F 0 0 (vectorWord x)
  have h01 := pairLift_translate F 1 0 (vectorWord x)
  have htwo : (1 : ZMod 2)+1=0 := by decide
  simp only [zero_add,htwo,h00,h10] at h11 h01
  fin_cases d <;> fin_cases l <;>
    simp [bellKernel,parityKernel_zero,parityKernel_one,Signature.equality,Signature.disequality,
      boolEquiv,bit,h00,h10,h11,h01] <;> ring

theorem signedNetwork_uses {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    Uses (cardFamily κ g) (signedNetwork F Γ g d l) := by
  apply stitch_uses
  · intro _
    exact Or.inr (Or.inr ⟨d,l,rfl⟩)
  · exact graphApply_uses Γ g

theorem signedNetwork_native {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    ∀ e,(signedNetwork F Γ g d l).edge e=Signature.disequality :=
  stitch_native _ _ (fun e => Fin.elim0 e) (graphApply_native Γ g)

@[simp] theorem signedNetwork_vertices {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    (signedNetwork F Γ g d l).shape.vertices=Γ.network.shape.vertices+2 := by
  simp [signedNetwork,Network.corolla]
  omega
@[simp] theorem signedNetwork_edges {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    (signedNetwork F Γ g d l).shape.edges=Γ.network.shape.edges+(n+2)+2 := by
  simp [signedNetwork,Network.corolla]

end
end Holant.ReedMuller.SignedRadon
