import Holant.Certificates.TetrahedralBridge.Normalization
import Holant.Certificates.MatchingProductBridge.ConeEmbedding
import Holant.Certificates.TetrahedralAffine.Interface

/-! Direct original-pair witnesses reject exactly the nine nonaffine
reconstructions in the proved twelve-element T map classification. Each
witness is a nonzero 2-by-2 minor on all three possible matching cuts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge

def normalizedParent (i : Fin 12) : Signature ℂ 6 :=
  TetrahedralBridge.reconstruct (TetrahedralBridge.sourceImages i)

def badIndex : Fin 9 → Fin 12 := ![0,1,2,3,4,5,9,10,11]

def badCard (i : Fin 9) : FourTensor := Signature.contract Q0
  (Tensor.reindex TetrahedralOrientation.contractOrder (normalizedParent (badIndex i)))

def minor (W : FourTensor) (r : Fin 3) (a b c d : Bool × Bool) : ℂ :=
  flatten r W a c * flatten r W b d - flatten r W a d * flatten r W b c

def minorWitness : Fin 9 → Fin 3 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  ![
    ![((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,true),(true,false))],
    ![((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,true),(true,false))],
    ![((false,false),(true,false),(false,false),(false,true)),((false,false),(true,false),(false,false),(false,true)),((false,true),(true,false),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(false,true))],
    ![((false,false),(false,true),(false,false),(false,true)),((false,false),(false,true),(false,false),(true,false)),((false,false),(false,true),(false,false),(true,false))]]

theorem matching_minor_zero (g : PlatonicModel) (W : FourTensor) (hW : matchingCone g W) :
    ∃ r : Fin 3, ∀ a b c d : Bool × Bool, minor W r a b c d=0 := by
  rcases matchingCone_presentation g W hW with rfl | ⟨r,U,V,hU,hV,rfl⟩
  · exact ⟨0,by intros; simp [minor]⟩
  · refine ⟨r,?_⟩
    intro a b c d
    fin_cases r <;>
      simp [minor,flatten,flatten0,flatten1,flatten2,matchingTensor,matchingProduct,P0,P1,P2] <;> ring

theorem bad_minor (i : Fin 9) (r : Fin 3) :
    minor (badCard i) r (minorWitness i r).1 (minorWitness i r).2.1
      (minorWitness i r).2.2.1 (minorWitness i r).2.2.2 ≠ 0 := by
  fin_cases i <;> fin_cases r <;>
    norm_num [minor,minorWitness,flatten,flatten0,flatten1,flatten2,badCard,badIndex,
      normalizedParent,Signature.contract,Tensor.reindex,TetrahedralOrientation.contractOrder,
      TetrahedralBridge.reconstruct,TetrahedralBridge.sourceImages,TetrahedralBridge.orderedTuple,
      TetrahedralBridge.ordered,TetrahedralBridge.candidate,TetrahedralBridge.regular,
      TetrahedralBridge.axisIndex,TetrahedralOrientation.axisR,TetrahedralOrientation.dual,
      A,B,C,P0,P1,P2,Q0,Q1,Q2,Q3,Signature.equality,Fin.sum_univ_succ,
      Fintype.sum_bool,Pi.smul_apply,smul_eq_mul] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.ext_iff]

theorem bad_not_matching (g : PlatonicModel) (i : Fin 9) : ¬matchingCone g (badCard i) := by
  intro h
  obtain ⟨r,hr⟩ := matching_minor_zero g _ h
  exact bad_minor i r (hr _ _ _ _)

theorem source_indices (i : Fin 12) :
    (∃ b : Fin 9,i=badIndex b) ∨ ∃ s : Fin 3,i=(s.castAdd 3).natAdd 6 := by
  fin_cases i
  · exact Or.inl ⟨0,rfl⟩
  · exact Or.inl ⟨1,rfl⟩
  · exact Or.inl ⟨2,rfl⟩
  · exact Or.inl ⟨3,rfl⟩
  · exact Or.inl ⟨4,rfl⟩
  · exact Or.inl ⟨5,rfl⟩
  · exact Or.inr ⟨0,rfl⟩
  · exact Or.inr ⟨1,rfl⟩
  · exact Or.inr ⟨2,rfl⟩
  · exact Or.inl ⟨6,rfl⟩
  · exact Or.inl ⟨7,rfl⟩
  · exact Or.inl ⟨8,rfl⟩

theorem preserving_parent (s : Fin 3) :
    normalizedParent ((s.castAdd 3).natAdd 6)=TetrahedralAffine.complexAncestor s := by
  fin_cases s <;> rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
end
