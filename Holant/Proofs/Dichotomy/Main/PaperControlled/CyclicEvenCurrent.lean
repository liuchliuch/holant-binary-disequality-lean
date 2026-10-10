import Holant.Proofs.Dichotomy.Main.PaperControlled.C2CanonicalPrime
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPairOutcome
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2QuaternaryCurrent
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicActualDeck
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2PrimeCurrent
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2KNormal

/-! An actual even cyclic endpoint is consumed without asking the caller for
a stable deck of that new gadget. A singular card installs its real unary
factor; otherwise complement reconstruction and the whole ordinary prime
consumer supply Eq4, tractability, or original-input hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.CyclicEvenCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace O
export GlobalCloseCompletionStopOrdinarySource (field table family presentation toOriginal)
end O
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace E
export PaperControlled.C2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (O.field G P) := (O.field G P).algebra'

inductive Outcome : Type 1 where
  | anchor (Q : Palette G) (old : P.family⊆Q.family) (eq4 : E.HasEq4 (O.table G Q))
  | tract (Q : Palette G) (old : P.family⊆Q.family) (criterion : Tract (O.family G Q))
  | hard (proof : PaperControlledHardness.Original G)
  | unary (Q : Palette G) (old : P.family⊆Q.family) (unary : RetainedUnary Q.family)

theorem retained_classified (f : Signature (OI.K G) 4)
    (retained : (⟨4,f⟩ : AnySignature (OI.K G))∈P.family)
    (prime : Prime (⟨4,f⟩ : AnySignature (OI.K G)))
    (even : Holant.Projective.CyclicQuaternary.EvenSupported f)
    (comp : ∀x,f x=f (fun i=>!(x i))) :
    E.HasEq4 (O.table G P) ∨ Tract (O.family G P) ∨ PaperControlledHardness.Original G := by
  let g := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f
  have ge : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport g := by
    intro x odd
    have parity : Holant.Projective.CyclicQuaternary.odd x=true := by
      rw [Holant.LocalDrafts.Hardness.EightVertexNonexception.word_eta x] at odd ⊢
      cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
      all_goals simp only [h0,h1,h2,h3] at odd ⊢
      all_goals first | rfl | exact False.elim (odd (by decide))
    change (ClosureSourceRows.embedding G) (f x)=0
    rw [even x parity,map_zero]
  have gc : ∀x,g x=g (fun i=>!(x i)) := fun x=>congrArg (ClosureSourceRows.embedding G) (comp x)
  have normal := GlobalCloseCompletionC2QuaternaryNormal.complementary_even g ge gc
  obtain ⟨N,equation⟩ := PaperControlled.C2QuaternaryCurrent.source_row G P f retained
  obtain ⟨z,literal⟩ := PaperControlled.C2QuaternaryCurrent.source_z G P
  have shape : GlobalCloseCompletionC2Q4Charts.Shape
      (RingHomRealization.mapSignature (O.field G P).subtype N.network.denote) := by
    rw [equation]
    change GlobalCloseCompletionC2Q4Charts.Shape (sourceKBasis.action g)
    rw [normal,GlobalCloseCompletionC2KNormal.sourceK_normal]
    exact Or.inl ⟨_,_,_,_,rfl⟩
  have mappedPrime : Prime (⟨4,g⟩ : AnySignature AlgebraicComplex) :=
    (prime_mapSignature_iff (ClosureSourceRows.embedding G) (⟨4,f⟩ : AnySignature (OI.K G))).mpr prime
  have tensorPrime := prime_coordinateAction ((PrimalityInterfaces.retained_equality_prime g).mp mappedPrime)
    (fun _=>sourceKBasis.matrix) (fun _=>sourceKBasis.inverse) (fun _=>sourceKBasis.inverse_matrix)
  have originalPrime : Prime (⟨4,N.network.denote⟩ : AnySignature (O.field G P)) := by
    apply (prime_mapSignature_iff (O.field G P).subtype (⟨4,N.network.denote⟩ : AnySignature (O.field G P))).mp
    apply (PrimalityInterfaces.retained_equality_prime _).mpr
    change TensorPrime (RingHomRealization.mapSignature (O.field G P).subtype N.network.denote)
    rw [equation]
    exact tensorPrime
  exact PaperControlled.C2CanonicalPrime.shape G (O.field G P) (O.presentation G P)
    (O.table G P) (O.toOriginal G P) z literal N shape originalPrime

variable (torsion : ResidualTorsion P.family)
variable (cyclic : IsCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

include cyclic in
theorem actual_classified (f : Signature (OI.K G) 4)
    (actual : Gadget.Realizes P.family .disequality f)
    (prime : Prime (⟨4,f⟩ : AnySignature (OI.K G)))
    (even : Holant.Projective.CyclicQuaternary.EvenSupported f) : Nonempty (Outcome G P) := by
  rcases GlobalCloseCompletionCyclicActualDeck.complement_or_singular P.family torsion P.equality
    (ClosurePhysicalBridge.complexEmbedding G) cyclic f actual with comp|⟨b,nonzero,bActual,singular⟩
  · let Q := ProgrammeSaturation.palette G P (⟨4,f⟩ : AnySignature (OI.K G)) prime.1 (by change 0<4;decide) actual
    have old : P.family⊆Q.family := ProgrammeSaturation.retains_old G P _ _ _ _
    have retained : (⟨4,f⟩ : AnySignature (OI.K G))∈Q.family :=
      ProgrammeSaturation.retains_output G P _ _ _ _
    rcases retained_classified G Q f retained prime even comp with anchor|tract|hard
    · exact ⟨.anchor Q old anchor⟩
    · exact ⟨.tract Q old tract⟩
    · exact ⟨.hard hard⟩
  · exact ⟨.unary (GlobalCloseCompletionCyclicActualDeck.palette G P b nonzero bActual)
      (GlobalCloseCompletionCyclicActualDeck.retains_old G P b nonzero bActual)
      (GlobalCloseCompletionCyclicActualDeck.retained_unary G P b nonzero bActual singular)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.CyclicEvenCurrent
end
