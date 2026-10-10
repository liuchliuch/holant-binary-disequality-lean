import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2TensorMatching
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortCurrent

/-! All ordered literal C2 cards are stable under genuine port permutations
and pointwise bit translations. These equalities allow finite tensor
normalization without changing any coefficient or assuming extra cards. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SafeSymmetry
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureSourceRows
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion
open GlobalCloseCompletionC2TensorMatching GlobalCloseCompletionC2ContractionReconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K I J : Type*} [Field K]

def Safe {m : ℕ} (f : Signature K (m+2)) : Prop :=
  ∀ (e : Equiv.Perm (Fin (m+2))) (p : Bool),
    LiteralMatching (Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f))

omit [Field K] in
theorem translate_reindex (mask : I → Bool) (e : I ≃ J) (f : Tensor K I) :
    Tensor.reindex e (translate mask f) =
      translate (fun j => mask (e.symm j)) (Tensor.reindex e f) := by
  funext w
  simp only [translate,Tensor.reindex,Equiv.symm_apply_apply]

private theorem xor_cons {m : ℕ} (mask : Fin (m+2) → Bool) (a b : Bool) (w : Fin m → Bool) :
    (fun i => (Fin.cons a (Fin.cons b w) : Fin (m+2) → Bool) i ^^ mask i) =
      Fin.cons (a ^^ mask 0) (Fin.cons (b ^^ mask 1) (fun i => w i ^^ mask i.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

theorem contract_translate {m : ℕ} (mask : Fin (m+2) → Bool) (f : Signature K (m+2)) (p : Bool) :
    Signature.contract (originalC2Binary p) (translate mask f) =
      translate (fun i => mask i.succ.succ)
        (Signature.contract (originalC2Binary ((p ^^ mask 0) ^^ mask 1)) f) := by
  funext w
  simp only [Signature.contract,translate]
  simp_rw [xor_cons]
  cases mask 0 <;> cases mask 1 <;> cases p <;>
    simp [originalC2Binary,X,Matrix.one_apply,Signature.disequality] <;> ring

theorem Safe.reindex {m : ℕ} {f : Signature K (m+2)} (h : Safe f)
    (e : Equiv.Perm (Fin (m+2))) : Safe (Tensor.reindex e f) := by
  intro q p
  exact h (q.trans e.symm) p

theorem Safe.translate {m : ℕ} {f : Signature K (m+2)} (h : Safe f)
    (mask : Fin (m+2) → Bool) : Safe (translate mask f) := by
  intro e p
  rw [translate_reindex,contract_translate]
  exact (h e ((p ^^ mask (e 0)) ^^ mask (e 1))).shift _

theorem Safe.map {m : ℕ} {f : Signature K (m+2)} (h : Safe f) (phi : K →+* ℂ) :
    Safe (RingHomRealization.mapSignature phi f) := by
  intro e p
  rw [←GlobalCloseCompletionC2SixPortCurrent.map_contract]
  exact (h e p).map phi

theorem current_safe [NumberField K] (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    {m : ℕ} (f : Signature K (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) : Safe f := by
  intro e p
  exact of_current F torsion hI cardTwo _
    (DeckContraction.orderedClosure_matching F torsion hI f stable e _
      (GlobalCloseCompletionC2CurrentComplement.kernel_member F torsion hI p))

/-- Some actual I/X card on one of three overlapping pairs is nonzero.
This uses reconstruction, rather than the unavailable four-kernel tomography. -/
theorem exists_live_card [CharZero K] (f : Signature K 6) (nonzero : f≠0) :
    ∃ e : Equiv.Perm (Fin 6), ∃ p : Bool,
      Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) ≠ 0 := by
  classical
  by_contra absent
  push Not at absent
  have zero (e : Equiv.Perm (Fin 6)) (w : Fin 6 → Bool) : pairSum f (e 0) (e 1) w = 0 := by
    rw [←GlobalCloseCompletionC2CurrentComplement.pairSum_reindex f e 0 1 w,
      GlobalCloseCompletionC2CurrentComplement.first_pairSum]
    rw [absent]
    rfl
  apply nonzero
  apply zero_of_pair_sums f 0 1 2
  · exact zero (Equiv.refl _)
  · simpa [Equiv.swap_apply_def] using zero (Equiv.swap (1 : Fin 6) 2)
  · simpa [Equiv.swap_apply_def] using zero ((Equiv.swap (0 : Fin 6) 1).trans (Equiv.swap 0 2))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SafeSymmetry
end
