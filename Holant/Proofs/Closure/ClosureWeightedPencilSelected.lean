import Holant.Proofs.Closure.ClosureWeightedPencilCurrent

/-! Closed shifted-A branch consumer. The actual source reflection, basis,
phase order and marked parameters are selected internally from source guards.
No successful sector classifier, gauge or analytic deck is a caller input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)

/-- Only the genuine marked-A branch guards and CURRENT stability are inputs.
The resulting original-field proper split has multiplier one. -/
theorem selected_current_six_split
    (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
      Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (noncyclic : ¬ IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
    (noZ : zClass ∉ ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)
    (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ left right : AnySignature (OI.K G),
      ((left.1=1 ∧ right.1=5) ∨ (left.1=2 ∧ right.1=4)) ∧
      ∃ result : ProperSplit (⟨6,f⟩ : AnySignature (OI.K G)) left right,result.scale=1 := by
  let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
  exact current_six_split G P torsion Q.basis (Q.selected axis notTwo notFour)
    (Q.parameters P.equality axis notTwo notFour noZ) rfl (by trivial)
    (Q.selected_range P.equality axis notTwo notFour) f nonzero stable

theorem selected_current_six_not_prime
    (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
      Subgroup.centralizer ({xClass} : Set (PGL2 ℂ)))
    (noncyclic : ¬ IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
    (noZ : zClass ∉ ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)
    (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ¬Prime (⟨6,f⟩ : AnySignature (OI.K G)) := by
  obtain ⟨left,right,_,split,_⟩ := selected_current_six_split G P torsion
    axis noncyclic notTwo notFour noZ f nonzero stable
  exact fun prime => prime.2 ⟨left,right,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
