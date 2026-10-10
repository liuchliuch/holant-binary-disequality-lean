import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMAlgebra
import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2BitTranslateActual

/-! The manuscript's four-copy H6-to-RM8 circuit is an actual finite gadget
in the original field. Every equality join is implemented using a retained I
vertex on native X wires. All four source multipliers survive explicitly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMActual
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace B
export GlobalCloseCompletionKleinH6RMBell (core core_algebraic)
end B
namespace A
export GlobalCloseCompletionKleinH6RMAlgebra (firstOrder secondOrder joinB joinC cycle cycle_scale)
end A
namespace I
export GlobalCloseCompletionC2BitTranslateActual (identity splice_identity)
end I
namespace R
export GlobalCloseCompletionC2RMActual (rm rm_algebraic)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]
variable (F : SignatureFamily K) (identity : RetainsIdentity F)

include identity in
theorem equality_contract_actual {n : ℕ} (f : Signature K (n+2))
    (actual : Gadget.Realizes F .disequality f) :
    Gadget.Realizes F .disequality (Signature.contract Signature.equality f) := by
  have hi : (⟨2,I.identity⟩ : AnySignature K)∈F := identity
  have flipped := realizes_splice F f I.identity actual
    (Gadget.realizes_of_mem F .disequality I.identity hi) (0 : Fin (n+2))
  rw [I.splice_identity] at flipped
  have joined := realizes_contract_exact_of_identity F identity _ flipped
  have equation : Signature.contract Signature.disequality
      (fun x : Fin (n+2)→Bool=>f (Function.update x 0 (!(x 0))))=
      Signature.contract Signature.equality f := by
    funext x
    rw [Signature.contract_disequality,Signature.contract_equality]
    simp only [Fin.cons_zero,Bool.not_false,Bool.not_true,Fin.update_cons_zero]
    exact add_comm _ _
  rwa [equation] at joined

include identity in
theorem joinB_actual (f g : Signature K 6) (left : Gadget.Realizes F .disequality f)
    (right : Gadget.Realizes F .disequality g) : Gadget.Realizes F .disequality (A.joinB f g) := by
  have tensor := realizes_tensor F .disequality f g left right
  have reordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality
    (Signature.tensor f g) tensor A.firstOrder.symm
  simp only [Equiv.symm_symm] at reordered
  exact equality_contract_actual F identity _ (equality_contract_actual F identity _ reordered)

include identity in
theorem joinC_actual (f g : Signature K 8) (left : Gadget.Realizes F .disequality f)
    (right : Gadget.Realizes F .disequality g) : Gadget.Realizes F .disequality (A.joinC f g) := by
  have tensor := realizes_tensor F .disequality f g left right
  have reordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality
    (Signature.tensor f g) tensor A.secondOrder.symm
  simp only [Equiv.symm_symm] at reordered
  exact equality_contract_actual F identity _ (equality_contract_actual F identity _
    (equality_contract_actual F identity _ (equality_contract_actual F identity _ reordered)))

include identity in
theorem cycle_actual (f : Signature K 6) (actual : Gadget.Realizes F .disequality f) :
    Gadget.Realizes F .disequality (A.cycle f) :=
  joinC_actual F identity _ _ (joinB_actual F identity f f actual actual)
    (joinB_actual F identity f f actual actual)

variable [CharZero K]

include identity in
theorem rm_actual (c : K) (nonzero : c≠0)
    (actual : Gadget.Realizes F .disequality (c • (B.core (K:=K)))) :
    ∃d : K,d≠0 ∧ Gadget.Realizes F .disequality (d • R.rm) := by
  refine ⟨32*c^4,mul_ne_zero (by norm_num) (pow_ne_zero 4 nonzero),?_⟩
  have h := cycle_actual F identity _ actual
  rwa [A.cycle_scale] at h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMActual
end
