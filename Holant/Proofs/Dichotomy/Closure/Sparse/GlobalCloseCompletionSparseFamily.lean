import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOTract
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenRowBasis
import Holant.Proofs.Closure.ClosureNativePresentation
import Holant.Proofs.Hardness.EONegativePairReduction

/-! Simultaneous class reconstruction for a finite family of sparse native-M
quaternaries. Their actual EO flip outputs share ONE sign and class; undoing
the independent physical flips preserves that same class on every original
row, at the native identity basis and its actual disequality edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome StableCurrentEvenEOTract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

/-- The selected pairing class, not a fresh singleton class, reconstructs
the entire complement-closed EO row. -/
theorem class_of_supports (M : Signature AlgebraicComplex 4)
    (eo : DenseEOUnitLocal.EOSupport M)
    (closed : ∀x,M (complementWord x)=0 ↔ M x=0)
    (sign : EOSign) (C : EOClass)
    (supports : EONegativeWitness.Supports sign ⟨4,M⟩)
    (pairings : EONegativeWitness.Pairings C ⟨4,M⟩) : C.Holds M := by
  obtain ⟨i,zero⟩ := missing_middle_of_supports M eo sign supports
  apply actual_class_of_opposite_zeros M eo C pairings i zero
  rw [FiveSupportEOOrdering.middleCoeff,←middleWord_complement]
  exact (closed (FiveSupportEOOrdering.middleWord i)).mpr zero

variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Fin t → Signature (OI.K G) 4) (core : Fin t → MinimumCore P.family)
variable (literal : ∀i,(core i).signature=⟨4,q i⟩)
variable (stable : ∀i,∀f∈rawDeck P.family torsion (q i),MatchingOrZero (actualTransfers P.family) f)
variable (d : ∀i,SparseOutput G P (q i) (core i) (literal i))

abbrev eoTable (i : Fin t) := eoRow G P (q i) (core i) (literal i) (d i)
abbrev eoFamily := EONegativePairReduction.family (a:=fun _ => 4) (eoTable G P q core literal d)
def originalFamily : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin t => (⟨4,embedded G (q i)⟩ : AnySignature AlgebraicComplex))

include N stable in
/-- The one class from the joint EO criterion is preserved on all original
noncentral sparse rows; the flip mask may differ between rows. -/
theorem simultaneous_class (tract : EOTract (eoFamily G P q core literal d)) :
    ∃C : EOClass,∀i : Fin t,C.Holds (embedded G (q i)) := by
  obtain ⟨_,_,sign,C,supports,pairings⟩ := tract
  refine ⟨C,fun i => ?_⟩
  have member : (⟨4,eoTable G P q core literal d i⟩ : AnySignature AlgebraicComplex)∈
      eoFamily G P q core literal d := ⟨i,rfl⟩
  have actual := class_of_supports (eoTable G P q core literal d i)
    (eoRow_support G P (q i) (core i) (literal i) (d i))
    (eoRow_complement_closed G P torsion N (q i) (core i) (literal i) (stable i) (d i))
    sign C (supports _ member) (pairings _ member)
  change C.Holds (eoRow G P (q i) (core i) (literal i) (d i)) at actual
  rw [eoRow_exact] at actual
  exact class_unflip C (embedded G (q i)) (d i).mask actual

include N stable in
/-- This is a common native family presentation, not a disjunction chosen
separately for each row. Both alternatives use the literal identity basis. -/
theorem simultaneous_basis (tract : EOTract (eoFamily G P q core literal d)) :
    IsCommonKBasis affineClass (originalFamily G q) InvertibleKernel.identity ∨
    IsCommonKBasis productClass (originalFamily G q) InvertibleKernel.identity := by
  obtain ⟨C,hC⟩ := simultaneous_class G P torsion N q core literal stable d tract
  cases C with
  | affine =>
      left
      refine ⟨?_,?_⟩
      · change Affine (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
        simpa [InvertibleKernel.identity,Kernel.pullback] using StableCurrentEvenRowBasis.native_edge_affine
      · rintro _ ⟨i,rfl⟩
        change Affine (InvertibleKernel.identity.symm.action (embedded G (q i)))
        simpa [EOClass.Holds] using hC i
  | product =>
      right
      refine ⟨?_,?_⟩
      · change Product (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
        simpa [InvertibleKernel.identity,Kernel.pullback] using StableCurrentEvenRowBasis.native_edge_product
      · rintro _ ⟨i,rfl⟩
        change Product (InvertibleKernel.identity.symm.action (embedded G (q i)))
        simpa [EOClass.Holds] using hC i

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseFamily
end
