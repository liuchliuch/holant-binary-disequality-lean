import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralAffineCards
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralClassifier

/-! A literal four-port matching presentation belongs to the same finite
Platonic matching cone. All original port orders and factor orientations
are retained; the finite check only enumerates bijections of four ports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicMatchingCone
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators

theorem ordered_pair_product (g : PlatonicModel) (p : (Fin 2 × Bool)≃Fin 4)
    (A B : Matrix Bool Bool ℂ) (hA : groupDirection g A) (hB : groupDirection g B) (c : ℂ) :
    matchingCone g (fun x=>c*(A (x (p (0,false))) (x (p (0,true)))*
      B (x (p (1,false))) (x (p (1,true))))) := by
  have cone (r : Fin 3) (U V : Matrix Bool Bool ℂ)
      (hU : groupDirection g U) (hV : groupDirection g V) :
      matchingCone g (fun x => c * matchingProduct r U V x) :=
    matchingCone_smul g (matchingProduct_mem_cone g r hU hV) c
  have ha : groupDirection g A.transpose := groupDirection_transpose g hA
  have hb : groupDirection g B.transpose := groupDirection_transpose g hB
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

theorem presentation (g : PlatonicModel) (M : Presentation ℂ (Fin 4))
    (member : ∀e,groupDirection g (M.matrix e)) : matchingCone g M.tensor := by
  have edges : M.edges=2 := by
    have h := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  cases M with
  | mk n ports matrix scalar =>
      dsimp only at edges
      subst n
      change matchingCone g (fun x => scalar * ∏ e : Fin 2,
        matrix e (x (ports (e,false))) (x (ports (e,true))))
      simpa [Fin.prod_univ_two,mul_assoc] using
        ordered_pair_product g ports (matrix 0) (matrix 1) (member 0) (member 1) scalar

open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (g : PlatonicModel) (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL g)

include literal in
theorem safe_direction (B : Matrix Bool Bool L) (safe : SafeBinary (actualTransfers F) B) :
    groupDirection g (B.map (complexEmbedding phi)) := by
  obtain ⟨C,hC,c,hc,he⟩ := safe
  have hB : B=c • C := by
    have ht := congrArg (fun A : Matrix Bool Bool L=>
      A*(Holant.Certificates.MatchingContractionClosure.X : Matrix Bool Bool L)) he
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using ht
  have h := GlobalCloseCompletionPlatonicCards.actual_direction phi F torsion g literal C hC
  rw [hB]
  have hm : (c • C).map (complexEmbedding phi)=complexEmbedding phi c • C.map (complexEmbedding phi) := by
    ext a b
    change (complexEmbedding phi) (c*C a b)=complexEmbedding phi c*complexEmbedding phi (C a b)
    exact map_mul _ _ _
  rw [hm]
  exact groupDirection_smul g h ((map_ne_zero _).mpr hc)

include literal in
theorem current_matching_cone (q : Signature L 4)
    (matching : MatchingOrZero (actualTransfers F) q) :
    matchingCone g (RingHomRealization.mapSignature (complexEmbedding phi) q) := by
  rcases matching with rfl | ⟨M,hM,_,rfl⟩
  · left
    funext x
    exact map_zero _
  · let N : Presentation ℂ (Fin 4) :=
      ⟨M.edges,M.ports,fun e=>(M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    have hN : ∀e,groupDirection g (N.matrix e) :=
      fun e=>safe_direction phi F torsion g literal (M.matrix e) (hM e)
    have he : RingHomRealization.mapSignature (complexEmbedding phi) M.tensor=N.tensor := by
      ext x
      simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]
    rw [he]
    exact presentation g N hN


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicMatchingCone
end
