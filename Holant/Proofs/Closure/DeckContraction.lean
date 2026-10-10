import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars
import Holant.Proofs.Closure.ContinuationTransport

/-! NEW UNVERIFIED all-arity ordered closure transport. Every safe kernel
has an explicit nonzero ORIGINAL-field scalar relative to a literal no-dressing
raw key. CURRENT rawDeck matching therefore supplies the first closure's
matching property, without a new universal-card premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckContraction
open Holant Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
variable {L : Type*} [Field L] {m : ℕ}

private theorem identity_actual (F : SignatureFamily L) (hI : RetainsIdentity F) :
    ActualNonsingular F (1 : Binary (K:=L)) := by
  refine ⟨?_,by simp⟩
  have hr := Gadget.realizes_of_mem F .disequality OrdinaryNormalization.identitySignature hI
  have he : OrdinaryNormalization.identitySignature =
      Holant.Projective.BoundedTorsion.binarySignature (1 : Binary (K:=L)) := by
    funext x
    simp [OrdinaryNormalization.identitySignature,Holant.Projective.BoundedTorsion.binarySignature,
      Matrix.one_apply,Signature.equality]
  exact he ▸ hr

private theorem dress_none {n : ℕ} (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (f : Signature L n) : dress F torsion f (fun _ => none) = f := by
  have h : ∀ (is : List (Fin n)) (g : Signature L n),
      is.foldl (fun g i => dressAt F torsion g (fun _ => none) i) g = g := by
    intro is
    induction is with
    | nil => exact fun _ => rfl
    | cons i is ih => exact fun g => ih g
  exact h (List.finRange n) f

/-- The exact ordered pair and residual order, with no omitted literal key. -/
def orderedKey (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (e : Equiv.Perm (Fin (m+2))) (j : completeGroup F torsion) : RawCardKey m (completeGroup F torsion) :=
  (fun _ => none,e,j,false)

theorem rawCard_ordered (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (f : Signature L (m+2)) (e : Equiv.Perm (Fin (m+2))) (j : completeGroup F torsion) :
    rawCard F torsion f (orderedKey F torsion e j) =
      Signature.contract (X * actualRepresentative F torsion j * X) (Tensor.reindex e.symm f) := by
  simp only [rawCard,orderedKey,orientBinary,Bool.false_eq_true,ite_false,dress_none]

/-- Original-L matrix equality for an arbitrary safe closure kernel. The
scalar need not itself be an uncharged source gadget; it remains recorded. -/
theorem safeKernel_representative (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (C : Binary (K:=L)) (safe : C ∈ actualTransfers F) :
    ∃ j : completeGroup F torsion, ∃ scalar : L, scalar ≠ 0 ∧
      C = scalar • (X * actualRepresentative F torsion j * X) := by
  obtain ⟨B,actual,d,hd,hC⟩ := safe
  let A : Binary (K:=L) := X*B
  have actualA : ActualNonsingular F A := by
    simpa only [A,Matrix.one_mul] using (identity_actual F hI).series actual
  obtain ⟨j,c,hc,representative⟩ := actual_binary_eq_representative F torsion A actualA
  have hCA : C = d • (X*A*X) := by
    rw [hC]
    change d • (B*X) = d • (X*(X*B)*X)
    simp only [←Matrix.mul_assoc,X_mul_X,Matrix.one_mul]
  refine ⟨j,d*c,mul_ne_zero hd hc,?_⟩
  rw [hCA,representative,Matrix.mul_smul,Matrix.smul_mul,smul_smul]

/-- Complete raw-key plus nonzero ORIGINAL-field scalar transport for ANY
ordered one-pair contraction by a safe kernel. No card closure is assumed. -/
theorem orderedClosure_raw_scalar (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (f : Signature L (m+2)) (e : Equiv.Perm (Fin (m+2)))
    (C : Binary (K:=L)) (safe : C ∈ actualTransfers F) :
    ∃ key : RawCardKey m (completeGroup F torsion), ∃ scalar : L, scalar ≠ 0 ∧
      Signature.contract C (Tensor.reindex e.symm f) = scalar • rawCard F torsion f key := by
  obtain ⟨j,c,hc,hC⟩ := safeKernel_representative F torsion hI C safe
  refine ⟨orderedKey F torsion e j,c,hc,?_⟩
  rw [hC,rawCard_ordered]
  simpa only [one_smul,mul_one] using ContinuationTransport.contract_smul
    (X * actualRepresentative F torsion j * X) (Tensor.reindex e.symm f) c 1

/-- CURRENT rawDeck matching is enough for this arbitrary safe first closure.
Zero raw cards stay zero under the same recorded nonzero scalar. -/
theorem orderedClosure_matching (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (e : Equiv.Perm (Fin (m+2))) (C : Binary (K:=L)) (safe : C ∈ actualTransfers F) :
    MatchingOrZero (actualTransfers F) (Signature.contract C (Tensor.reindex e.symm f)) := by
  obtain ⟨key,c,hc,he⟩ := orderedClosure_raw_scalar F torsion hI f e C safe
  rw [he]
  exact ContinuationTransport.matching_smul (stable _ (Or.inr ⟨key,rfl⟩)) c hc

end Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckContraction
