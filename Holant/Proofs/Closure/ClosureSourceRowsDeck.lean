import Holant.Proofs.Closure.ClosureSourceRows
import Holant.Proofs.Closure.ContinuationTransport

/-! Every ordered q4 source card is a literal no-dressing raw key. The source
field, selected closing representative, all 24 ordered port permutations,
zero branch and recorded scalar are preserved. This bridge supplies no row
normalization or subgroup classifier as a hidden premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open RingHomRealization
variable {L : Type*} [Field L]

theorem dress_none {n : ℕ} (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (g : Signature L n) : dress F torsion g (fun _ => none) = g := by
  have h : ∀ (is : List (Fin n)) (q : Signature L n),
      is.foldl (fun f i => dressAt F torsion f (fun _ => none) i) q = q := by
    intro is
    induction is with
    | nil => exact fun _ => rfl
    | cons i is ih => exact fun q => ih q
  exact h (List.finRange n) g

/-- All deleted-pair and residual orders are kept in this literal key. -/
def orderedKey (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (e : Equiv.Perm (Fin 4)) (j : completeGroup F torsion) :
    RawCardKey 2 (completeGroup F torsion) := (fun _ => none,e,j,false)

theorem rawCard_ordered (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4) (e : Equiv.Perm (Fin 4)) (j : completeGroup F torsion) :
    rawCard F torsion q (orderedKey F torsion e j) =
      Signature.contract (X * actualRepresentative F torsion j * X)
        (Tensor.reindex e.symm q) := by
  simp only [rawCard, orderedKey, orientBinary, Bool.false_eq_true, ite_false, dress_none]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)

/-- Matrix equality, not merely projective agreement. The physical native-X
sandwich is the same one in the complete literal raw-key catalogue. -/
theorem sourceCard_raw (e : Equiv.Perm (Fin 4)) (j : completeGroup P.family torsion) :
    Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
      (representative G P torsion j) =
        (binaryMatrix (rawCard P.family torsion q (orderedKey P.family torsion e j))).map
          (embedding G) := by
  rw [rawCard_ordered]
  funext u v
  have hwords (a b : Bool) :
      (Fin.cons a (Fin.cons b (![u,v] : Fin 2 → Bool)) : Fin 4 → Bool) = ![a,b,u,v] := by
    funext i
    fin_cases i <;> rfl
  simp only [Holant.Marked.SupportAtlas.physicalCard,Holant.Marked.SupportAtlas.contract0,
    Holant.Marked.SupportAtlas.reorder,
    RingHomRealization.mapSignature,representative,binaryMatrix,Matrix.map_apply,
    Signature.contract,Tensor.reindex,map_sum,map_mul,hwords]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Kernel.disequality_sandwich]
  congr 1
  exact congrArg (embedding G)
    (nativePair_apply (actualRepresentative P.family torsion j) a b).symm

/-- Exact ordered-card coverage by the current deck, including its zero
cards; the physical catalogue is constructed internally by its literal key. -/
theorem sourceCard_in_rawDeck (e : Equiv.Perm (Fin 4)) (j : completeGroup P.family torsion) :
    rawCard P.family torsion q (orderedKey P.family torsion e j) ∈ rawDeck P.family torsion q :=
  Or.inr ⟨orderedKey P.family torsion e j,rfl⟩

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

/-- Each exact source card already has a concrete current-source graph,
including a zero card, before any analytic normalization is attempted. -/
def orderedCardDirect (e : Equiv.Perm (Fin 4)) (j : completeGroup P.family torsion) :
    DeckDirect P.family (rawCard P.family torsion q (orderedKey P.family torsion e j)) :=
  deckRawDirect G P torsion q core hcore (orderedKey P.family torsion e j)

def orderedCardAccess (e : Equiv.Perm (Fin 4)) (j : completeGroup P.family torsion) :
    CurrentSignatureAccess G P
      ⟨2,rawCard P.family torsion q (orderedKey P.family torsion e j)⟩ :=
  currentSignatureAccess G P _ (orderedCardDirect G P torsion q core hcore e j).realizes

@[simp] theorem orderedCardAccess_same_controlled (e : Equiv.Perm (Fin 4))
    (j : completeGroup P.family torsion) :
    (orderedCardAccess G P torsion q core hcore e j).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P _
        (orderedCardAccess G P torsion q core hcore e j).power := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
