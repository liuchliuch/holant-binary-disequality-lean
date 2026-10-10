import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralChart
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCards
import Holant.Proofs.Closure.ClosureFactorTreeAction
import Holant.Platonic.TetrahedralLocalization.OneStep

/-! Exact all-arity marked O pair cards in their analytic Clifford chart.
Every card comes from the actual original full deck with a nonzero multiplier;
the chart transports the same matching incidence and all binary factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChartCards
open Holant Holant.Tractable Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.TetrahedralLocalization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry ClosureMarkedDihedral.Source
open GlobalCloseCompletionOctahedralChart
open scoped BigOperators
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (form : Form) (literal : group phi F torsion=Coordinates.Models.group form)

include literal in
theorem safe_direction (B : Matrix Bool Bool L) (safe : SafeBinary (actualTransfers F) B) :
    Direction form (B.map (complexEmbedding phi)) := by
  obtain ⟨C,hC,c,hc,he⟩ := safe
  have hB : B=c • C := by
    have ht := congrArg (fun A : Matrix Bool Bool L=>A*Holant.Certificates.MatchingContractionClosure.X) he
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using ht
  have h := GlobalCloseCompletionOctahedralCards.actual_direction phi F torsion form literal C hC
  rw [hB]
  have hm : (c • C).map (complexEmbedding phi)=complexEmbedding phi c • C.map (complexEmbedding phi) := by
    ext a b
    exact map_mul (complexEmbedding phi) c (C a b)
  rw [hm]
  exact h.smul ((map_ne_zero _).mpr hc)

include literal in
theorem matching_presentation {n : ℕ} (q : Signature L n)
    (matching : MatchingOrZero (actualTransfers F) q) :
    RingHomRealization.mapSignature (complexEmbedding phi) q=0 ∨
      ∃M : Presentation ℂ (Fin n),(∀e,Direction form (M.matrix e)) ∧
        RingHomRealization.mapSignature (complexEmbedding phi) q=M.tensor := by
  rcases matching with rfl | ⟨M,hM,_,rfl⟩
  · left; funext x; exact map_zero _
  · let N : Presentation ℂ (Fin n) :=
      ⟨M.edges,M.ports,fun e=>(M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    refine Or.inr ⟨N,fun e=>safe_direction phi F torsion form literal _ (hM e),?_⟩
    ext x
    simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]

variable {m : ℕ} (f : Signature L (m+2))
variable (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)

include literal stable in
theorem actual_pair (p : (Bool ⊕ Fin m)≃Fin (m+2))
    (K : Matrix Bool Bool ℂ) (member : Direction form K) :
    ∃q : Signature L m,MatchingOrZero (actualTransfers F) q ∧
      ∃c : ℂ,c≠0 ∧ RingHomRealization.mapSignature (complexEmbedding phi) q=
        c • pairCard p K (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionOctahedralCards.kernel_alignment
    phi F torsion form literal K member
  let B := actualRepresentative F torsion j
  let e : Equiv.Perm (Fin (m+2)) := (firstPair m).symm.trans p
  let key : RawCardKey m (completeGroup F torsion) := (fun _=>none,e,j,false)
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
  have hword (a b : Bool) (x : Fin m→Bool) :
      (fun i : Fin (m+2)=>(Fin.cons a (Fin.cons b x) : Fin (m+2)→Bool) (e.symm i))=
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
  exact ⟨rawCard F torsion f key,stable _ (Or.inr ⟨key,rfl⟩),c,hc,mapped⟩

theorem pair_as_contract {n : ℕ} (p : (Bool ⊕ Fin n)≃Fin (n+2))
    (K : Matrix Bool Bool ℂ) (q : Signature ℂ (n+2)) :
    pairCard p K q=Signature.contract K (Tensor.reindex (p.symm.trans (firstPair n)) q) := by
  ext x
  simp only [pairCard,LinearMap.coe_mk,AddHom.coe_mk,Signature.contract,Tensor.reindex]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  ext i
  change pairInsert p a b x i=(Fin.cons (α:=fun _=>Bool) a (Fin.cons (α:=fun _=>Bool) b x)) ((firstPair n) (p.symm i))
  rw [←pairInsert_firstPair]
  simp [pairInsert]

theorem pair_action {n : ℕ} (f : Form) (p : (Bool ⊕ Fin n)≃Fin (n+2))
    (K : Matrix Bool Bool ℂ) (q : Signature ℂ (n+2)) :
    pairCard p K (action f q)=action f (pairCard p ((H f).transpose*K*H f) q) := by
  have hk : pairKernel (H f) (H f) K=(H f).transpose*K*H f := by
    ext a b
    simp only [pairKernel,Kernel.mul,Kernel.transpose,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_bool]
    ring
  rw [pair_as_contract,action,reindex_action,contract_action,pair_as_contract,hk]
  rfl

private theorem action_scale {n : ℕ} (form : Form) (c : ℂ) (q : Signature ℂ n) :
    action form (c • q)=c • action form q := by
  funext x
  unfold action Signature.coordinateAction
  change (∑y,(∏j,H form (x j) (y j))*(c*q y))=c*(∑y,(∏j,H form (x j) (y j))*q y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

include literal stable in
theorem chart_pair_affine (p : (Bool ⊕ Fin m)≃Fin (m+2))
    (K : Matrix Bool Bool ℂ) (member : groupDirection .octahedral K) :
    ComplexAffine (pairCard p K (action form (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  obtain ⟨q,hq,c,hc,he⟩ := actual_pair phi F torsion form literal f stable p
    ((H form).transpose*K*H form) (pair_direction form K member)
  have ha : ComplexAffine (action form (RingHomRealization.mapSignature (complexEmbedding phi) q)) := by
    rcases matching_presentation phi F torsion form literal q hq with zero | ⟨M,hM,eq⟩
    · rw [zero,action,Signature.coordinateAction_zero]
      exact affine_zero_complex
    · rw [eq]
      exact presentation_affine form M hM
  rw [he,action_scale] at ha
  rw [pair_action]
  exact (affine_complex_scale_iff c hc _).mp ha

include literal in
theorem chart_pair_cone (f : Signature L 6)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)
    (p : (Bool ⊕ Fin 4)≃Fin 6) (K : Matrix Bool Bool ℂ)
    (member : groupDirection .octahedral K) :
    matchingCone .octahedral
      (pairCard p K (action form (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  obtain ⟨q,hq,c,hc,he⟩ := actual_pair phi F torsion form literal f stable p
    ((H form).transpose*K*H form) (pair_direction form K member)
  have ha : matchingCone .octahedral
      (action form (RingHomRealization.mapSignature (complexEmbedding phi) q)) := by
    rcases matching_presentation phi F torsion form literal q hq with zero | ⟨M,hM,eq⟩
    · rw [zero,action,Signature.coordinateAction_zero]
      exact matchingCone_zero _
    · rw [eq]
      exact presentation_cone form M hM
  rw [he,action_scale] at ha
  rw [pair_action]
  have hu := matchingCone_smul .octahedral ha c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChartCards
end
