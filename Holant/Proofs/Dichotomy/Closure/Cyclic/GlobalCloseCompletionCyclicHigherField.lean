import Holant.Proofs.Closure.ClosureMarkedCyclic
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CurrentComplement
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortCurrent

/-! Actual cyclic complete groups have the fixed I/X transfer span, and
ordered source matching cards transport faithfully to the complex field.
No coordinate change, C2 cardinality, or literal-factor premise is imposed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherField
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open RingHomRealization
namespace B
export ClosureFieldBridgeGroups (mappedTorsion actualTransfers_map transfer_map)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

/-- Actual matrix lifts of one cyclic projective group commute exactly. -/
theorem cyclic_lifts_commute (H : Subgroup (PGL2 ℂ)) [IsCyclic H]
    (U V : Matrix.GeneralLinearGroup Bool ℂ) (hU : pglMk ℂ U∈H) (hV : pglMk ℂ V∈H) :
    (U : Matrix Bool Bool ℂ)*(V : Matrix Bool Bool ℂ)=
      (V : Matrix Bool Bool ℂ)*(U : Matrix Bool Bool ℂ) := by
  obtain ⟨q,hq⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨W,hW⟩ := QuotientGroup.mk'_surjective (scalarSubgroup ℂ) q
  have power (A : Matrix.GeneralLinearGroup Bool ℂ) (hA : pglMk ℂ A∈H) :
      ∃k : ℤ,∃c : ℂ,c≠0 ∧ (A : Matrix Bool Bool ℂ)=c • (↑(W^k) : Matrix Bool Bool ℂ) := by
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp (hq.symm ▸ hA)
    have he : pglMk ℂ A=pglMk ℂ (W^k) := by
      rw [map_zpow]
      change pglMk ℂ A=(QuotientGroup.mk' (scalarSubgroup ℂ) W)^k
      rw [hW]
      exact hk.symm
    obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
    exact ⟨k,c,hc,he⟩
  obtain ⟨i,c,_hc,hu⟩ := power U hU
  obtain ⟨j,d,_hd,hv⟩ := power V hV
  have he : (↑(W^i) : Matrix Bool Bool ℂ)*(↑(W^j) : Matrix Bool Bool ℂ)=
      (↑(W^j) : Matrix Bool Bool ℂ)*(↑(W^i) : Matrix Bool Bool ℂ) :=
    congrArg Units.val (zpow_mul_comm W i j)
  rw [hu,hv]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [he,mul_comm c d]

theorem actual_span (F : SignatureFamily ℂ) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cyclic : IsCyclic (completeGroup F torsion))
    (T : Binary (K:=ℂ)) (hT : T∈actualTransfers F) :
    ∃a b : ℂ,T=fun u v=>a*Signature.equality u v+b*Signature.disequality u v := by
  letI := cyclic
  have hg := actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero T (hg.det_ne_zero hT)
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero (X : Binary (K:=ℂ)) det_X_ne_zero
  have hx : (X : Binary (K:=ℂ))∈actualTransfers F := by
    refine ⟨1,ClosureSourceRows.identity_actual F hI,1,one_ne_zero,?_⟩
    simp [transfer]
  have commute := cyclic_lifts_commute (completeGroup F torsion) U V ⟨U,hT,rfl⟩ ⟨V,hx,rfl⟩
  change T*X=X*T at commute
  have h00 := congrFun₂ commute false false
  have h01 := congrFun₂ commute false true
  have diagonal : T false false=T true true := by
    simpa [Matrix.mul_apply,X,Signature.disequality] using h01
  have opposite : T false true=T true false := by
    simpa [Matrix.mul_apply,X,Signature.disequality] using h00
  refine ⟨T false false,T false true,?_⟩
  ext u v
  cases u <;> cases v <;> simp [Signature.equality,Signature.disequality,diagonal,opposite]

variable {K I : Type*} [Field K]
theorem matching_map (phi : K→+*ℂ) (F : SignatureFamily K) (f : Tensor K I)
    (matching : MatchingOrZero (actualTransfers F) f) :
    MatchingOrZero (actualTransfers (mapFamily phi F)) (fun x=>phi (f x)) := by
  rcases matching with rfl|⟨M,valid,nonzero,rfl⟩
  · left
    funext x
    exact map_zero phi
  · right
    refine ⟨⟨M.edges,M.ports,fun i=>(M.matrix i).map phi,phi M.scalar⟩,?_,
      (map_ne_zero phi).mpr nonzero,?_⟩
    · intro i
      change transfer ((M.matrix i).map phi)∈actualTransfers (mapFamily phi F)
      rw [B.transfer_map]
      exact B.actualTransfers_map phi (valid i)
    · funext x
      simp only [Presentation.tensor,productValue,map_mul,map_prod,Matrix.map_apply]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicHigherField
end
