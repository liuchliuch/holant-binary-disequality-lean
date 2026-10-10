import Holant.Proofs.Closure.ClosureCompatibleAlignmentCards

/-! The selected protected edge need not already be the first two residual
ports.  Its literal original endpoints determine a shared coordinate order.
The original deleted pair is fixed, and the frozen CompatibleCards fields
are then satisfied exactly, rather than weakened to projective port equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.EndpointParallelogram

variable {r : ℕ}

def protectedOrder (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    Equiv.Perm (Fin (2*r+2)) := pairOrder (p (e,false)) (p (e,true))

theorem protectedOrder_first (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    protectedOrder p e 0 = p (e,false) := by
  apply pairOrder_first
  intro same
  have h := congrArg Prod.snd (p.injective same)
  cases h

theorem protectedOrder_second (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    protectedOrder p e 1 = p (e,true) := pairOrder_second _ _

theorem contract_liftPair (p : Equiv.Perm (Fin (2*r+2)))
    (f : Signature Scalar (2*r+4)) (K : Mat) :
    Signature.contract K (Tensor.reindex (liftPair p).symm f) =
      Tensor.reindex p.symm (Signature.contract K f) := by
  funext x
  simp only [Signature.contract,Tensor.reindex,word_liftPair]

theorem pairing_reindex (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (order : Equiv.Perm (Fin (2*r+2))) (u : Fin (2*r+2)) :
    (Pairing.ofPorts (p.trans order.symm)).mate u =
      order.symm ((Pairing.ofPorts p).mate (order u)) := by
  simp [Pairing.ofPorts]

theorem alignedTables_reindex
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (order : Equiv.Perm (Fin (2*r+2))) :
    alignedTables (fun b => (p b).trans order.symm) A = alignedTables p A := by
  funext b e
  cases b
  · rfl
  · simp [alignedTables,alignedFactor,edgeIndex,edgeReversed]
    rfl

/-- This factory accepts the actual chosen edge index and derives the one
shared order, both physical card realizations, full scalar identities and the
literal protected (2,3) boundary.  The local common-parity premise stays visible. -/
def fromSelectedProductsAt {m : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (f : Signature Scalar (2*r+4))
    (actual : Gadget.Realizes F .disequality f)
    (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots m t})
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (κ : Bool → Scalar)
    (nonzero : ∀ b,κ b ≠ 0)
    (equation : ∀ b,Signature.contract (M (sector b) (phase b).val) f =
      productValue (p b) (A b) (κ b))
    (same : (Pairing.ofPorts (p false)).mate = (Pairing.ofPorts (p true)).mate)
    (e : Fin (r+1)) (parity : Fin (r+1) → Bool)
    (sameParity : ∀ b j,HasParity (parity j) (alignedTables p A b j)) :
    CompatibleCards G (Tensor.reindex (liftPair (protectedOrder (p false) e)).symm f) := by
  let order := protectedOrder (p false) e
  let ports := fun b => (p b).trans order.symm
  refine fromSelectedProducts G _ (realizes_reindex F .disequality f actual (liftPair order))
    sector phase ports A κ nonzero ?_ ?_ e ?_ ?_ parity ?_
  · intro b
    rw [contract_liftPair,equation b]
    rfl
  · funext u
    rw [pairing_reindex,pairing_reindex]
    rw [same]
  · change order.symm (p false (e,false)) = 0
    rw [← protectedOrder_first (p false) e]
    exact order.symm_apply_apply 0
  · change order.symm (p false (e,true)) = 1
    rw [← protectedOrder_second (p false) e]
    exact order.symm_apply_apply 1
  · intro b j
    rw [alignedTables_reindex]
    exact sameParity b j

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
