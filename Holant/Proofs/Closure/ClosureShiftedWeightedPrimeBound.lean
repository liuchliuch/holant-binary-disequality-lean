import Holant.Proofs.Closure.ClosureShiftedWeightedFamilyAssembly

/-! Closed original-source prime exclusion in the higher shifted weighted
branch. The actual source prime internally yields its saved anchor; CURRENT
outside products produce a real standard-ancestor split; inverse transport
preserves source primeness, giving the contradiction. No anchor, root deck,
model, common family certificate or split is supplied to the closed branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)

include sameBasis nonstandard stable order in
/-- Original-field CURRENT source prime of arity≥8 is impossible in this
constructed weighted sector. Every source anchor and line bound is internal. -/
theorem current_not_prime (large : 2 ≤ r) : ¬Prime (⟨2*r+4,f⟩ : AnySignature (OI.K G)) := by
  intro prime
  let receipt := primeAnchorReceipt G P torsion U N params f order sameBasis nonstandard stable
    (by omega) ⟨r+1,by omega⟩ prime
  let A := receipt.source
  obtain ⟨e,R,split,ports,unit⟩ := currentStandard_split G P torsion U N params f order A
    sameBasis nonstandard stable large
  have hp := standardAncestor_prime G P torsion U N params f order
    (anchoredGaugeReceipt G P torsion U N params f order sameBasis nonstandard stable (by omega) ⟨r+1,by omega⟩ A) prime
  change Prime (⟨2*r+4,currentStandard G P torsion U N params f order A sameBasis nonstandard stable large⟩ : AnySignature Scalar) at hp
  exact hp.2 ⟨_,_,⟨split⟩⟩

include stable order in
/-- All shifted coordinates, reflection phases and marked parameters are
produced from the actual source guards. No desired conjugator/model is input. -/
theorem selected_shifted_not_prime
    (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
      Subgroup.centralizer ({Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.xClass} : Set (PGL2 ℂ)))
    (noncyclic : ¬ IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
    (noZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass ∉
      ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)
    (large : 2 ≤ r) : ¬Prime (⟨2*r+4,f⟩ : AnySignature (OI.K G)) := by
  let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
  exact current_not_prime G P torsion Q.basis (Q.selected axis notTwo notFour)
    (Q.parameters P.equality axis notTwo notFour noZ) f order rfl (by trivial) stable large

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
