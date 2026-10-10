import Holant.Proofs.Closure.ClosureCyclicCurrentExit
import Holant.Proofs.Closure.ClosureCyclicCurrentPreservation
import Holant.Proofs.Closure.GroupPreparedStability
import Holant.Proofs.FiniteGroups.Stabilization.ExactGroupBound

/-! Same-original-field q4 cyclic restart state and exact copied-tree maps.
No future producer, group or rank decrease is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure Copy (P Q : Palette G) where
  label : Fin P.count → Fin Q.count
  injective : Function.Injective label
  saved : ∀ i,Frontier.paletteRoot G Q (label i)=Frontier.paletteRoot G P i

namespace Copy
variable {G}

def identity (P : Palette G) : Copy G P P := ⟨id,Function.injective_id,fun _ => rfl⟩

def comp {P Q R : Palette G} (A : Copy G P Q) (B : Copy G Q R) : Copy G P R :=
  ⟨B.label ∘ A.label,B.injective.comp A.injective,
    fun i => (B.saved (A.label i)).trans (A.saved i)⟩

theorem retains {P Q : Palette G} (A : Copy G P Q) : P.family ⊆ Q.family := by
  rintro f ⟨i,rfl⟩
  exact ⟨A.label i,congrArg Sigma.fst (A.saved i)⟩

def occurrence {P Q : Palette G} (A : Copy G P Q) (o : CurrentOccurrences.Id G P) :
    CurrentOccurrences.Id G Q := ⟨A.label o.1,Occurrences.transportAddress (A.saved o.1).symm o.2⟩

theorem occurrence_leaf {P Q : Palette G} (A : Copy G P Q) (o : CurrentOccurrences.Id G P) :
    CurrentOccurrences.savedLeaf G Q (A.occurrence o)=CurrentOccurrences.savedLeaf G P o :=
  Occurrences.transportAddress_leaf (A.saved o.1).symm o.2

theorem occurrence_injective {P Q : Palette G} (A : Copy G P Q) : Function.Injective A.occurrence := by
  rintro ⟨i,p⟩ ⟨j,q⟩ equal
  have labels : A.label i=A.label j := congrArg Sigma.fst equal
  have same := A.injective labels
  subst j
  have addresses : Occurrences.transportAddress (A.saved i).symm p=
      Occurrences.transportAddress (A.saved i).symm q :=
    @sigma_mk_injective (Fin Q.count) (fun k => Occurrences.Address (Q.trees k)) (A.label i) _ _ equal
  exact Sigma.ext rfl (heq_of_eq (Occurrences.transportAddress_injective (A.saved i).symm addresses))

end Copy

structure Node : Type 1 where
  palette : Palette G
  torsion : ResidualTorsion palette.family
  q : Signature (OI.K G) 4
  core : MinimumCore palette.family
  literal : core.signature=⟨4,q⟩
  noUnary : ¬RetainedUnary palette.family
  noOdd : StabilizationMathematical.NoOdd palette.family
  matching : ∀ g ∈ rawDeck palette.family torsion q,MatchingOrZero (actualTransfers palette.family) g

namespace Node
variable (S : Node G)

def exit : StructuralExit G S.palette :=
  .stable 2 S.q (by decide) (by decide) S.torsion S.core S.literal S.noUnary S.noOdd S.matching

def rank : ℕ := sourceGroupDefect S.palette.family S.torsion

theorem nonbinary : ∃ f ∈ S.palette.family,Prime f ∧ 3≤f.1 :=
  ⟨S.core.signature,S.core.retained,S.core.prime,S.core.nonbinary⟩

end Node

def Earlier (T S : Node G) : Prop := T.rank G < S.rank G

theorem earlier_wellFounded : WellFounded (Earlier G) :=
  InvImage.wf (fun S : Node G => S.rank G) Nat.lt_wfRel.wf

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
end
