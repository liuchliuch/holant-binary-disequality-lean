import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOneSidedMiddle

/-! Literal native port orders select any live middle coefficient while
preserving the two endpoints and even support. The selected row is an actual
one-vertex output over the complete original table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrders
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end C
namespace P
export GeneralCancellationCapPin (portOrder)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K]

def reordered (q : Signature K 4) (k : Fin 6) : Signature K 4 := Tensor.reindex (P.portOrder k false) q

def MiddleLive (q : Signature K 4) : Prop :=
  (entries q).b≠0 ∨ (entries q).c≠0 ∨ (entries q).d≠0 ∨
    (entries q).w≠0 ∨ (entries q).z≠0 ∨ (entries q).y≠0

theorem first (q : Signature K 4) (k : Fin 6) : (entries (reordered q k)).a=(entries q).a := by
  apply congrArg q
  funext i
  fin_cases k <;> fin_cases i <;> rfl

theorem last (q : Signature K 4) (k : Fin 6) : (entries (reordered q k)).x=(entries q).x := by
  apply congrArg q
  funext i
  fin_cases k <;> fin_cases i <;> rfl

theorem middle (q : Signature K 4) (k : Fin 6) :
    (entries (reordered q k)).y= ![(entries q).y,(entries q).z,(entries q).w,
      (entries q).d,(entries q).c,(entries q).b] k := by
  fin_cases k <;> apply congrArg q
  all_goals funext i;fin_cases i <;> rfl

theorem weight_order : ∀k : Fin 6,∀x : Fin 4→Bool,weight (fun i=>x (P.portOrder k false i))=weight x := by
  decide +kernel

theorem even (q : Signature K 4) (h : EvenSupport q) (k : Fin 6) : EvenSupport (reordered q k) := by
  intro x odd
  apply h
  rwa [weight_order]

theorem selected (q : Signature K 4) (live : MiddleLive q) :
    ∃k : Fin 6,(entries (reordered q k)).y≠0 := by
  rcases live with b|c|d|w|z|y
  · exact ⟨5,by rw [middle];exact b⟩
  · exact ⟨4,by rw [middle];exact c⟩
  · exact ⟨3,by rw [middle];exact d⟩
  · exact ⟨2,by rw [middle];exact w⟩
  · exact ⟨1,by rw [middle];exact z⟩
  · exact ⟨0,by rw [middle];exact y⟩

variable {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (q : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩) (k : Fin 6)

def output : NativeAntiTargetSource.Output H 4 where
  network:=C.reindex (Network.corolla q) (P.portOrder k false)
  labels:={vertex _:=label
           vertex_arity _:=congrArg Sigma.fst literal
           edge:=Fin.elim0}
  exact:=fun _=>literal
  native:=fun e=>Fin.elim0 e

theorem output_value : (output H q label literal k).network.denote=reordered q k := by
  rw [output,C.reindex_denote,Network.denote_corolla]
  rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrders
end
