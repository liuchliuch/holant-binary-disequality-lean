import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicMatchingCone
import Holant.Certificates.RainbowOrbit.ExternalDeckIntegration

/-! Any literal four-port presentation over the external-T group belongs to
its exact matching deck. This supplies the existing no-rainbow theorem with
actual factors, original port orders and all nonzero scalar multipliers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCone
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators

def Cone (F : FourTensor) : Prop := F=0 ∨ ∃r : Fin 3,RainbowOrbit.External.InMatching r F

theorem product_mem (r : Fin 3) {U V : Matrix Bool Bool ℂ}
    (hU : RainbowOrbit.External.Direction U) (hV : RainbowOrbit.External.Direction V) :
    Cone (matchingProduct r U V) :=
  Or.inr ⟨r,U,V,hU,hV,(matchingTensor_eq_product r U V).symm⟩

theorem cone_smul {F : FourTensor} (hF : Cone F) (c : ℂ) : Cone (c • F) := by
  by_cases hc : c=0
  · exact Or.inl (by simp [hc])
  rcases hF with rfl | ⟨r,U,V,hU,hV,rfl⟩
  · exact Or.inl (smul_zero _)
  · exact Or.inr ⟨r,c • U,V,hU.smul hc,hV,(matchingTensor_smul_left r c U V).symm⟩

theorem ordered_pair_product (p : (Fin 2 × Bool)≃Fin 4)
    (A B : Matrix Bool Bool ℂ) (hA : RainbowOrbit.External.Direction A) (hB : RainbowOrbit.External.Direction B) (c : ℂ) :
    Cone (fun x=>c*(A (x (p (0,false))) (x (p (0,true)))*
      B (x (p (1,false))) (x (p (1,true))))) := by
  have cone (r : Fin 3) (U V : Matrix Bool Bool ℂ)
      (hU : RainbowOrbit.External.Direction U) (hV : RainbowOrbit.External.Direction V) :
      Cone (fun x => c * matchingProduct r U V x) :=
    cone_smul (product_mem r hU hV) c
  have ha : RainbowOrbit.External.Direction A.transpose := RainbowOrbit.External.Direction.transpose hA
  have hb : RainbowOrbit.External.Direction B.transpose := RainbowOrbit.External.Direction.transpose hB
  have h01 : p (0,false)≠p (0,true) := p.injective.ne (by decide)
  have h02 : p (0,false)≠p (1,false) := p.injective.ne (by decide)
  have h03 : p (0,false)≠p (1,true) := p.injective.ne (by decide)
  have h12 : p (0,true)≠p (1,false) := p.injective.ne (by decide)
  have h13 : p (0,true)≠p (1,true) := p.injective.ne (by decide)
  have h23 : p (1,false)≠p (1,true) := p.injective.ne (by decide)
  generalize hp0 : p (0,false)=a0 at h01 h02 h03 h12 h13 h23 ⊢
  generalize hp1 : p (0,true)=a1 at h01 h02 h03 h12 h13 h23 ⊢
  generalize hp2 : p (1,false)=a2 at h01 h02 h03 h12 h13 h23 ⊢
  generalize hp3 : p (1,true)=a3 at h01 h02 h03 h12 h13 h23 ⊢
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;>
    try omega
  all_goals first
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 A B hA hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 A.transpose B ha hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 A B.transpose hA hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 A.transpose B.transpose ha hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 B A hB hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 B.transpose A hb hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 B A.transpose hB ha)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 0 B.transpose A.transpose hb ha)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 A B hA hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 A.transpose B ha hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 A B.transpose hA hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 A.transpose B.transpose ha hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 B A hB hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 B.transpose A hb hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 B A.transpose hB ha)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 1 B.transpose A.transpose hb ha)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 A B hA hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 A.transpose B ha hB)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 A B.transpose hA hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 A.transpose B.transpose ha hb)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 B A hB hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 B.transpose A hb hA)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 B A.transpose hB ha)
    | simpa [matchingProduct,P0,P1,P2,Matrix.transpose_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        (cone 2 B.transpose A.transpose hb ha)

theorem presentation (M : Presentation ℂ (Fin 4))
    (member : ∀e,RainbowOrbit.External.Direction (M.matrix e)) : Cone M.tensor := by
  have edges : M.edges=2 := by
    have h := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  cases M with
  | mk n ports matrix scalar =>
      dsimp only at edges
      subst n
      have he : (Presentation.mk 2 ports matrix scalar).tensor=
          (fun x=>scalar*(matrix 0 (x (ports (0,false))) (x (ports (0,true)))*
            matrix 1 (x (ports (1,false))) (x (ports (1,true))))) := by
        funext x
        simp only [Presentation.tensor,productValue,Fin.prod_univ_two]
      rw [he]
      exact ordered_pair_product ports (matrix 0) (matrix 1) (member 0) (member 1) scalar

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCone
end
