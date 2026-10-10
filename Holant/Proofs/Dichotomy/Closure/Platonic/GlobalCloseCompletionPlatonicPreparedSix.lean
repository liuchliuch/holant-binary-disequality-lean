import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicMatchingCone
import Holant.Platonic.TetrahedralLocalization.OneStep

/-! Actual six-port Platonic preparation from the complete current raw deck.
Every ordered pair and every literal Platonic kernel has a matching-cone output,
with its original-field representative and exact nonzero scale retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicPreparedSix
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.TetrahedralLocalization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (g : Holant.Certificates.MatchingProductBridge.PlatonicModel)
variable (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL g)
variable (f : Signature L 6)
variable (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)

include literal stable in
theorem pair_matching (p : (Bool ⊕ Fin 4)≃Fin 6)
    (K : Matrix Bool Bool ℂ) (member : groupDirection g K) :
    matchingCone g (pairCard p K (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionPlatonicCards.kernel_alignment
    phi F torsion g literal K member
  let B := actualRepresentative F torsion j
  let e : Equiv.Perm (Fin 6) := (firstPair 4).symm.trans p
  let key : RawCardKey 4 (completeGroup F torsion) := (fun _=>none,e,j,false)
  have hraw : rawCard F torsion f key=
      Signature.contract (nativePair B) (Tensor.reindex e.symm f) := by
    simp only [rawCard,key,orientBinary,Bool.false_eq_true,ite_false,ClosureSourceRows.dress_none]
    rfl
  have hpair : nativePair (B.map (complexEmbedding phi))=c • K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair K (!a) (!b)=c*K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hkernel (a b : Bool) : complexEmbedding phi (nativePair B a b)=c*K a b := by
    rw [nativePair_apply]
    have hh := congrFun (congrFun hpair a) b
    rw [nativePair_apply] at hh
    change complexEmbedding phi (B (!a) (!b))=c*K a b at hh
    exact hh
  have hword (a b : Bool) (x : Word 4) :
      (fun i : Fin 6=>(Fin.cons a (Fin.cons b x) : Word 6) (e.symm i))=
        pairInsert p a b x := by
    ext i
    obtain ⟨u,rfl⟩ := p.surjective i
    cases u with
    | inl t => cases t <;> simp [e,firstPair,pairInsert]
    | inr j => simp [e,firstPair,pairInsert]
  have mapped : RingHomRealization.mapSignature (complexEmbedding phi) (rawCard F torsion f key)=
      c • pairCard p K (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
    rw [hraw]
    ext x
    simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
      hkernel,hword,pairCard,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have cone := GlobalCloseCompletionPlatonicMatchingCone.current_matching_cone
    phi F torsion g literal (rawCard F torsion f key)
      (stable _ (Or.inr ⟨key,rfl⟩))
  rw [mapped] at cone
  have unscaled := matchingCone_smul g cone c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using unscaled

include literal stable in
theorem literal_prepared : ∀ i : Fin (Holant.Certificates.RainbowOrbit.size g),
    matchingCone g (Signature.contract (Holant.Certificates.RainbowOrbit.representative g i)
      (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  intro i
  have h := pair_matching phi F torsion g literal f stable (firstPair 4)
    (Holant.Certificates.RainbowOrbit.representative g i)
    (Holant.Certificates.RainbowOrbit.representative_mem g i)
  convert h using 1
  funext x
  simp only [pairCard,LinearMap.coe_mk,AddHom.coe_mk,Signature.contract,pairInsert_firstPair]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicPreparedSix
end
