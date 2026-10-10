import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralStabilizer
import Holant.Projective.CyclicQuaternary.Physical
import Holant.Certificates.OctahedralSeparator.TensorTransport

/-! Coefficient extraction from the preserved marked-octahedral proof. Four independently oriented actual legs act on the
SAME ordered q4 card map. This is a tensor identity, not an endpoint or
normal-form premise. In particular the two transposes are forced by the
original input/output port positions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
open Holant Holant.Certificates Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open Holant.LocalDrafts.MainChain RingHomRealization
open scoped Matrix BigOperators

theorem map_action {K M : Type*} [CommSemiring K] [CommSemiring M]
    (ρ : K →+* M) {n : ℕ} (A : Fin n → Kernel K) (q : Signature K n) :
    RingHomRealization.mapSignature ρ (Signature.coordinateAction A q) =
      Signature.coordinateAction (fun i u v => ρ (A i u v)) (RingHomRealization.mapSignature ρ q) := by
  funext x
  simp only [RingHomRealization.mapSignature,Signature.coordinateAction,map_sum,map_mul,map_prod]

theorem action_slot_scalars {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n → Kernel K) (c : Fin n → K) (q : Signature K n) :
    Signature.coordinateAction (fun i => c i • A i) q =
      (∏ i,c i) • Signature.coordinateAction A q := by
  funext x
  simp [Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib,Finset.mul_sum,mul_assoc]

/-- Native-X splice and coefficient embedding commute before comparison
with any target form. This consumes the OLD original-L splice proof. -/

theorem sum_four (f : (Fin 4 → Bool) → ℂ) :
    (∑ x,f x) = ∑ a : Bool,∑ b : Bool,∑ c : Bool,∑ d : Bool,f ![a,b,c,d] := by
  simp only [Holant.ReedMuller.CoefficientAtlas.sum_words_succ,Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1

private theorem binary_action (N U V : BinaryMatrix) (c d : Bool) :
    Signature.coordinateAction ![U,V] (fun x : Fin 2→Bool=>N (x 0) (x 1)) ![c,d] =
      (U*N*V.transpose) c d := by
  unfold Signature.coordinateAction
  rw [← (piFinTwoEquiv (fun _ : Fin 2=>Bool)).symm.sum_comp]
  simp [Fintype.sum_prod_type,Fin.prod_univ_two,piFinTwoEquiv,
    Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_bool]
  ring

private theorem contract_rawCard (q : FourTensor) (K : BinaryMatrix) :
    Signature.contract K q=(fun x : Fin 2→Bool=>rawCard q (Equiv.refl _) K (x 0) (x 1)) := by
  funext x
  have hx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hx]
  rfl

/-- The original four ordered tensor slots force U^T K V at the input,
and W (card K) Z^T at the output. No Hermitian conjugation occurs. -/
theorem contraction_dressing (q : FourTensor) (U V W Z K : BinaryMatrix) :
    rawCard (Signature.coordinateAction ![U,V,W,Z] q) (Equiv.refl _) K =
      W * rawCard q (Equiv.refl _) (U.transpose*K*V) * Z.transpose := by
  ext c d
  have h := congrFun (OctahedralSeparator.contract_action ![U,V,W,Z] K q) ![c,d]
  have hk : OctahedralSeparator.pairKernel U V K=U.transpose*K*V :=
    (Matrix.mul_assoc U.transpose K V).symm
  have hl : (fun j : Fin 2=>(![U,V,W,Z] : Fin 4→Kernel ℂ) j.succ.succ)=![W,Z] := by
    funext j
    fin_cases j <;> rfl
  change rawCard (Signature.coordinateAction ![U,V,W,Z] q) (Equiv.refl _) K c d =
    Signature.coordinateAction (fun j : Fin 2=>(![U,V,W,Z] : Fin 4→Kernel ℂ) j.succ.succ)
      (Signature.contract (OctahedralSeparator.pairKernel U V K) q) ![c,d] at h
  rw [hl,hk,contract_rawCard,binary_action] at h
  exact h

theorem card_dressing (q : FourTensor) (U V W Z : BinaryMatrix) :
    cardMatrix (Signature.coordinateAction ![U,V,W,Z] q) =
      sandwich W Z.transpose * cardMatrix q * sandwich U.transpose V := by
  apply matrix_ext_action
  intro v
  have ha (f : FourTensor) : cardMatrix f *ᵥ v =
      coordinates (rawCard f (Equiv.refl _) (assemble v)) := by
    have h := GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_action f (assemble v)
    have hv : coordinates (assemble v)=v := coordinates.apply_symm_apply v
    change cardMatrix f *ᵥ coordinates (assemble v)=
      coordinates (rawCard f (Equiv.refl _) (assemble v)) at h
    rw [hv] at h
    exact h
  rw [ha,contraction_dressing]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    sandwich_action U.transpose V v,
    Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.cardMatrix_action,
    sandwich_action]
  change coordinates (W*rawCard q (Equiv.refl _) (U.transpose*assemble v*V)*Z.transpose) =
    coordinates (W*assemble (quaternionCoefficient
      (rawCard q (Equiv.refl _) (U.transpose*assemble v*V)))*Z.transpose)
  rw [assemble_coefficient]

theorem tensor_dressing (q : FourTensor) (U V W Z : BinaryMatrix) :
    Signature.coordinateAction ![U,V,W,Z] q =
      reconstruct (sandwich W Z.transpose * cardMatrix q * sandwich U.transpose V) := by
  rw [← card_dressing]
  exact (reconstruct_cardMatrix _).symm

/-- Internally selected image and dual cells supply the four root indices.
These are forward orbit actions; this definition does NOT promise that
the result is normalized or an endpoint. -/
def orbitCodes (l r : Fin 122) : Fin 4 → Fin 24 :=
  ![(orbitPair r).1,(orbitPair r).2,(orbitPair l).1,(orbitPair l).2]

def orbitReverse : Fin 4 → Bool := ![true,false,false,true]

def stabilizerCodes (k : Fin 8) : Fin 4 → Fin 24 :=
  ![0,0,(stabilizerPair k).1,(stabilizerPair k).2]

def orbitSandwich (f : Holant.Certificates.OctahedralSeparator.Form) (t : Fin 122) : End :=
  sandwich (kernel f (orbitPair t).1) (kernel f (orbitPair t).2)

/-- SAME q4 map transported by the internally computed LEFT/RIGHT kernel
pairs. The right-X wrapper is retained, rather than dropped or recast. -/
theorem orbit_tensor (f : Holant.Certificates.OctahedralSeparator.Form)
    (q : FourTensor) (l r : Fin 122) :
    Signature.coordinateAction (fun i => if orbitReverse i then
      (kernel f (orbitCodes l r i)).transpose else kernel f (orbitCodes l r i)) q =
      reconstruct (orbitSandwich f l * rightX * transferMatrix q (Equiv.refl _) *
        orbitSandwich f r) := by
  have hs : (fun i => if orbitReverse i then
      (kernel f (orbitCodes l r i)).transpose else kernel f (orbitCodes l r i)) =
      ![(kernel f (orbitPair r).1).transpose,kernel f (orbitPair r).2,
        kernel f (orbitPair l).1,(kernel f (orbitPair l).2).transpose] := by
    funext i
    fin_cases i <;> rfl
  have ht : rightX * transferMatrix q (Equiv.refl _) = cardMatrix q := by
    change rightX * (rightX*cardMatrix (relabel (Equiv.refl _) q)) = _
    rw [← Matrix.mul_assoc,rightX_square,Matrix.one_mul]
    rfl
  rw [hs,tensor_dressing,Matrix.transpose_transpose,Matrix.transpose_transpose]
  simp only [orbitSandwich,Matrix.mul_assoc,ht]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
