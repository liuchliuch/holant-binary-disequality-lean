import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBSparseSource
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBPrimeEq4

/-! Consume the positive sparse-B class immediately into a real labelled
Eq4 graph for the normalized whole-current source. A selected sparse q4 is
only an actual occurrence; the common A/P class is constructed by the joint
EO criterion, or the result is original-G hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBSparseEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open FixedGadgetSubstitution Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Q
export GlobalCloseCompletionBQuaternary (normalized identity_member SparseOutput)
end Q
namespace S
export GlobalCloseCompletionBSparseSource (graph uses labels eoTable complement_closed simultaneous_class_or_hard)
end S
namespace Codec
export GlobalCloseCompletionBNativeCodec (mapped)
end Codec
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Fin t → Signature (OI.K G) 4) (core : Fin t → MinimumCore P.family)
variable (literal : ∀i,(core i).signature=⟨4,q i⟩)
variable (stable : ∀i,∀f∈rawDeck P.family torsion (q i),MatchingOrZero (actualTransfers P.family) f)
variable (d : ∀i,Q.SparseOutput G P (q i))

include N core literal stable d in
theorem fromSelected (i : Fin t) (C : EOClass) (member : C.Holds (Q.normalized G (q i))) :
    Nonempty (GlobalCloseCompletionBPrimeEq4.Output (Codec.mapped G P)) := by
  let j := (Q.identity_member G P).choose
  have hj : (⟨GlobalCloseCompletionBNativeSource.arity G P j.val,Codec.mapped G P j⟩ :
      AnySignature AlgebraicComplex)=⟨2,GlobalCloseCompletionSparseEq4Flip.identity⟩ :=
    (Q.identity_member G P).choose_spec
  apply GlobalCloseCompletionBPrimeEq4.class_output (Codec.mapped G P) j hj
    (S.graph G P q d i) (S.labels G P q core literal d i)
    (fun v => (S.uses G P q core literal d i v).choose_spec)
    (Flip.native _ _) ?_ ?_ ?_ C ?_
  · rw [Flip.denote]
    exact (d i).eo
  · rw [Flip.denote]
    exact (d i).prime
  · rw [Flip.denote]
    exact S.complement_closed G P torsion N q core literal stable d i
  · rw [Flip.denote]
    exact StableCurrentEvenEOTract.class_flip C _ (d i).mask member

include N core literal stable d in
theorem eq4_or_hard (i : Fin t) :
    Nonempty (GlobalCloseCompletionBPrimeEq4.Output (Codec.mapped G P)) ∨
      StableCurrentEvenLocalOutcome.OriginalHard G := by
  rcases S.simultaneous_class_or_hard G P torsion N q core literal stable d with ⟨C,member⟩ | hard
  · exact Or.inl (fromSelected G P torsion N q core literal stable d i C (member i))
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBSparseEq4
end
