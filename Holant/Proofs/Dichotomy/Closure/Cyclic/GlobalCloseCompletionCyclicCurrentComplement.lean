import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherDeck
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2QuaternaryNormal

/-! A cyclic current group forces simultaneous complement invariance of
all stable prime-sized rows. Safe factors may have both parity sectors;
no even-support or order-two assertion is made by this theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicCurrentComplement
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureSourceRows GlobalCloseCompletionC2ContractionReconstruction
namespace Old
export GlobalCloseCompletionC2CurrentComplement (first_pairSum pairSum_reindex kernel_member)
end Old
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (phi : K→+*ℂ)
variable (cyclic : IsCyclic (completeGroup (RingHomRealization.mapFamily phi F)
  (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
include torsion hI cyclic in
theorem safe_binary_complement (B : Binary (K:=K))
    (safe : SafeBinary (actualTransfers F) B) (a b : Bool) : B a b=B (!a) (!b) := by
  have hm : transfer (B.map phi)∈actualTransfers (RingHomRealization.mapFamily phi F) := by
    rw [ClosureFieldBridgeGroups.transfer_map]
    exact ClosureFieldBridgeGroups.actualTransfers_map phi safe
  obtain ⟨c,d,he⟩ := GlobalCloseCompletionCyclicHigherField.actual_span _
    (ClosureFieldBridgeGroups.mappedTorsion phi F torsion) (GlobalCloseCompletionCyclicHigherDeck.identity_map phi hI) cyclic _ hm
  have e0 := congrFun₂ he false true
  have e1 := congrFun₂ he true false
  have e2 := congrFun₂ he false false
  have e3 := congrFun₂ he true true
  simp [transfer,Matrix.mul_apply,Matrix.map_apply,X,Signature.equality,Signature.disequality] at e0 e1 e2 e3
  apply phi.injective
  cases a <;> cases b
  · exact e0.trans e1.symm
  · exact e2.trans e3.symm
  · exact e3.trans e2.symm
  · exact e1.trans e0.symm

include torsion hI cyclic in
theorem matching_complement {I : Type*} (f : Tensor K I)
    (matching : MatchingOrZero (actualTransfers F) f) (w : I→Bool) :
    f w=f (fun i=>!(w i)) := by
  rcases matching with rfl|⟨M,valid,_hc,rfl⟩
  · rfl
  · simp only [Presentation.tensor,productValue]
    apply congrArg (M.scalar * ·)
    apply Finset.prod_congr rfl
    intro i _
    exact safe_binary_complement F torsion hI phi cyclic (M.matrix i) (valid i) _ _

include torsion hI cyclic in
theorem ordered_card_complement {m : ℕ} (f : Signature K (m+2))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)
    (e : Equiv.Perm (Fin (m+2))) (p : Bool) (w : Fin m→Bool) :
    Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) w=
      Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) (fun i=>!(w i)) :=
  matching_complement F torsion hI phi cyclic _
    (DeckContraction.orderedClosure_matching F torsion hI f stable e _
      (Old.kernel_member F torsion hI p)) w

include torsion hI cyclic in
theorem ordered_pairSum_complement {m : ℕ} (f : Signature K (m+2))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)
    (e : Equiv.Perm (Fin (m+2))) (w : Fin (m+2)→Bool) :
    pairSum f (e 0) (e 1) w=pairSum f (e 0) (e 1) (fun i=>!(w i)) := by
  rw [←Old.pairSum_reindex f e 0 1 w,
    ←Old.pairSum_reindex f e 0 1 (fun i=>!(w i)),Old.first_pairSum,Old.first_pairSum]
  have hp : (!(w (e 0)) ^^ !(w (e 1)))=(w (e 0) ^^ w (e 1)) := by
    cases w (e 0) <;> cases w (e 1) <;> rfl
  rw [hp]
  exact ordered_card_complement F torsion hI phi cyclic f stable e _ _

include torsion hI cyclic in
theorem current_complement {m : ℕ} (f : Signature K (m+3))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    ∀w,f w=f (fun i=>!(w i)) := by
  have h2 : 2%(m+3)=2 := Nat.mod_eq_of_lt (by omega)
  apply complement_of_pair_sums f 0 1 2
  · exact ordered_pairSum_complement F torsion hI phi cyclic f stable (Equiv.refl _)
  · have h:=ordered_pairSum_complement F torsion hI phi cyclic f stable (Equiv.swap (1 : Fin (m+3)) 2)
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using h
  · have h:=ordered_pairSum_complement F torsion hI phi cyclic f stable
      ((Equiv.swap (0 : Fin (m+3)) 1).trans (Equiv.swap 0 2))
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using h

include torsion hI cyclic in
theorem even_normal (f : Signature K 4)
    (even : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport f)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    f=GlobalCloseCompletionKleinTwistedAlgebra.normal (f ![false,false,false,false])
      (f ![false,false,true,true]) (f ![false,true,false,true]) (f ![false,true,true,false]) :=
  GlobalCloseCompletionC2QuaternaryNormal.complementary_even f even
    (current_complement F torsion hI phi cyclic f stable)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicCurrentComplement
end
