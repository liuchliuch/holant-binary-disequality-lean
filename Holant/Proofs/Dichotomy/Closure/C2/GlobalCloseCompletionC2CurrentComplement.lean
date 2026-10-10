import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2ContractionReconstruction
import Holant.Proofs.Closure.DeckContraction

/-! Actual order-two raw-deck consequences in the original coefficient field.
Safe matching factors are scalar literal I/X matrices, hence every matching
card is invariant under simultaneous complementation of its residual ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CurrentComplement
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureSourceRows GlobalCloseCompletionC2ContractionReconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 32768
set_option Elab.async false
variable {L : Type*} [Field L]
private theorem cons_word {m : ℕ} (w : Fin (m+2) → Bool) :
    Fin.cons (w 0) (Fin.cons (w 1) (fun i : Fin m => w i.succ.succ)) = w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

private theorem flip_first {m : ℕ} (w : Fin (m+2) → Bool) :
    GlobalCloseCompletionC2ContractionReconstruction.flip w 0 1 = Fin.cons (!w 0) (Fin.cons (!w 1) (fun i : Fin m => w i.succ.succ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [GlobalCloseCompletionC2ContractionReconstruction.flip]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [GlobalCloseCompletionC2ContractionReconstruction.flip]
    · simp [GlobalCloseCompletionC2ContractionReconstruction.flip,Fin.ext_iff]

/-- The coefficient pair sum is one literal I/X card, with its actual residual
word and no factor or nonzero assumption. -/
theorem first_pairSum {m : ℕ} (f : Signature L (m+2)) (w : Fin (m+2) → Bool) :
    pairSum f 0 1 w = Signature.contract (originalC2Binary (w 0 ^^ w 1)) f
      (fun i : Fin m => w i.succ.succ) := by
  rw [pairSum,flip_first]
  conv_lhs => lhs; rw [←cons_word w]
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    simp [Signature.contract,originalC2Binary,X,Matrix.one_apply,Signature.disequality]
  all_goals exact add_comm _ _

theorem pairSum_reindex {m : ℕ} (f : Signature L m) (e : Equiv.Perm (Fin m))
    (i j : Fin m) (w : Fin m → Bool) :
    pairSum (Tensor.reindex e.symm f) i j (fun t => w (e t)) =
      pairSum f (e i) (e j) w := by
  simp only [pairSum,Tensor.reindex,Equiv.apply_symm_apply]
  congr 1
  apply congrArg f
  funext t
  simp [GlobalCloseCompletionC2ContractionReconstruction.flip,Equiv.symm_apply_eq]

variable [NumberField L]
variable (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion) = 2)
include torsion hI cardTwo

theorem safe_binary_complement (B : Binary (K := L))
    (safe : SafeBinary (actualTransfers F) B) (a b : Bool) : B a b = B (!a) (!b) := by
  obtain ⟨j,c,hc,he⟩ := safe_binary_eq_representative F torsion B safe
  obtain ⟨p,d,hd,hm⟩ := c2_actual_binary F torsion hI cardTwo
    (actualRepresentative F torsion j) (actualRepresentative_actual F torsion j)
  rw [he,hm]
  cases p <;> cases a <;> cases b <;>
    simp [originalC2Binary,X,Signature.disequality]

theorem matching_complement {I : Type*} (f : Tensor L I)
    (matching : MatchingOrZero (actualTransfers F) f) (w : I → Bool) :
    f w = f (fun i => !w i) := by
  rcases matching with rfl | ⟨M,valid,_hc,rfl⟩
  · rfl
  · simp only [Presentation.tensor,productValue]
    apply congrArg (M.scalar * ·)
    apply Finset.prod_congr rfl
    intro i _hi
    exact safe_binary_complement F torsion hI cardTwo (M.matrix i) (valid i) _ _

omit cardTwo in
theorem kernel_member (p : Bool) : originalC2Binary (L := L) p ∈ actualTransfers F := by
  cases p
  · exact (actualTransfers_projectiveMatrixGroup F (actualTransfers_nonempty F) torsion).one_mem
  · refine ⟨1,identity_actual F hI,1,one_ne_zero,?_⟩
    simp [originalC2Binary,transfer]

theorem ordered_card_complement {m : ℕ} (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (e : Equiv.Perm (Fin (m+2))) (p : Bool) (w : Fin m → Bool) :
    Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) w =
      Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f) (fun i => !w i) := by
  exact matching_complement F torsion hI cardTwo _
    (DeckContraction.orderedClosure_matching F torsion hI f stable e _
      (kernel_member F torsion hI p)) w

theorem ordered_pairSum_complement {m : ℕ} (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (e : Equiv.Perm (Fin (m+2))) (w : Fin (m+2) → Bool) :
    pairSum f (e 0) (e 1) w = pairSum f (e 0) (e 1) (fun i => !w i) := by
  rw [←pairSum_reindex f e 0 1 w,
    ←pairSum_reindex f e 0 1 (fun i => !w i),first_pairSum,first_pairSum]
  have hp : (!w (e 0) ^^ !w (e 1)) = (w (e 0) ^^ w (e 1)) := by
    cases w (e 0) <;> cases w (e 1) <;> rfl
  rw [hp]
  exact ordered_card_complement F torsion hI cardTwo f stable e _ _

/-- The actual stable order-two raw deck forces simultaneous complement
invariance of the entire original-field tensor, in every arity at least three. -/
theorem current_complement {m : ℕ} (f : Signature L (m+3))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) :
    ∀ w, f w = f (fun i => !w i) := by
  have h2 : 2 % (m+3) = 2 := Nat.mod_eq_of_lt (by omega)
  apply complement_of_pair_sums f 0 1 2
  · exact ordered_pairSum_complement F torsion hI cardTwo f stable (Equiv.refl _)
  · have h := ordered_pairSum_complement F torsion hI cardTwo f stable
      (Equiv.swap (1 : Fin (m+3)) 2)
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using h
  · have h := ordered_pairSum_complement F torsion hI cardTwo f stable
      ((Equiv.swap (0 : Fin (m+3)) 1).trans (Equiv.swap 0 2))
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CurrentComplement
end
