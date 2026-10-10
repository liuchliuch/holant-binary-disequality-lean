import Holant.Proofs.Closure.FrontierCurrentClosure
import Holant.Proofs.Closure.OccurrenceMinimumScope
import Holant.Proofs.Algorithms.PrimalityInterfaces

/-! RECONSTRUCTED recovery of the previously kernel-checked q4 adapter.
A retained prime of arity four really is minimum under CURRENT noOdd.
Higher-even occurrences retain their separate preparation obligations. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierQ4
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization

def tableFour {L : Type*} (f : AnySignature L) (arity : f.1 = 4) : Signature L 4 := arity ▸ f.2

theorem tableFour_exact {L : Type*} (f : AnySignature L) (arity : f.1 = 4) :
    (⟨4,tableFour f arity⟩ : AnySignature L) = f := by
  rcases f with ⟨n,f⟩
  dsimp only at arity
  subst n
  rfl

/-- Arity four is the smallest possible nonbinary even prime arity. -/
def minimumOfFour {L : Type*} [Field L] (F : SignatureFamily L) (f : AnySignature L)
    (retained : f ∈ F) (prime : Prime f) (arity : f.1 = 4)
    (noOdd : ∀ g ∈ F, Prime g → 3 ≤ g.1 → Even g.1) : MinimumCore F where
  signature := f
  retained := retained
  prime := prime
  nonbinary := by rw [arity]; omega
  minimum := by
    intro g hg hp hn
    have he := noOdd g hg hp hn
    rcases he with ⟨k,hk⟩
    rw [arity]
    omega

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (o : CurrentOccurrences.Id G P)

def embeddedTable (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4) : Signature AlgebraicComplex 4 :=
  fun x => Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G
    (tableFour (CurrentOccurrences.savedLeaf G P o).1 arity x)

theorem embedded_tensorPrime (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4) :
    Holant.Certificates.EqualityQuaternary.TensorPrime (embeddedTable G P o arity) := by
  apply (Holant.LocalDrafts.MainChain.PrimalityInterfaces.retained_equality_prime _).mp
  have hp : Prime (⟨4,tableFour (CurrentOccurrences.savedLeaf G P o).1 arity⟩ : AnySignature (OI.K G)) := by
    rw [tableFour_exact]
    exact CurrentOccurrences.savedLeaf_prime G P o
  exact (prime_mapSignature_iff (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom
    (⟨4,tableFour (CurrentOccurrences.savedLeaf G P o).1 arity⟩ : AnySignature (OI.K G))).mpr hp

structure Domain (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4) where
  minimum : MinimumCore P.family
  literal : minimum.signature = (CurrentOccurrences.savedLeaf G P o).1
  current : CurrentOccurrences.Domain G P o
  currentExact : current = (CurrentOccurrences.domain G P o).withMinimum G minimum literal
  algebraicTable : Signature AlgebraicComplex 4
  algebraicExact : algebraicTable = embeddedTable G P o arity
  tensorPrime : Holant.Certificates.EqualityQuaternary.TensorPrime algebraicTable

def domain (arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4)
    (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1) : Domain G P o arity :=
  let core := minimumOfFour P.family (CurrentOccurrences.savedLeaf G P o).1
    (CurrentOccurrences.savedLeaf_retained G P o) (CurrentOccurrences.savedLeaf_prime G P o) arity noOdd
  ⟨core,rfl,(CurrentOccurrences.domain G P o).withMinimum G core rfl,rfl,
    embeddedTable G P o arity,rfl,embedded_tensorPrime G P o arity⟩

variable {G P o}
variable {arity : (CurrentOccurrences.savedLeaf G P o).1.1 = 4}

def Domain.toOriginal (d : Domain G P o arity) := d.current.toOriginal G
def Domain.fromOriginal (d : Domain G P o arity) := d.current.fromOriginal G

theorem domain_saved_exact (d : Domain G P o arity) :
    (⟨4,tableFour d.minimum.signature (d.literal ▸ arity)⟩ : AnySignature (OI.K G)) =
      (CurrentOccurrences.savedLeaf G P o).1 :=
  (tableFour_exact _ _).trans d.literal

def Domain.algebraicMinimum (d : Domain G P o arity) :
    MinimumCore (CurrentFrontierClosure.currentFamily G P) :=
  d.minimum.mapField (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom

theorem domain_algebraicMinimum_literal (d : Domain G P o arity) :
    d.algebraicMinimum.signature = (⟨4,d.algebraicTable⟩ : AnySignature AlgebraicComplex) := by
  change mapSignature (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom d.minimum.signature = _
  rw [d.literal, ← tableFour_exact (CurrentOccurrences.savedLeaf G P o).1 arity]
  rw [d.algebraicExact]
  rfl

theorem domain_toOriginal_controlled (d : Domain G P o arity) :
    d.toOriginal.controlled = P.toOriginal.controlled := rfl

theorem domain_fromOriginal_controlled (d : Domain G P o arity) :
    d.fromOriginal.controlled = P.fromOriginal.controlled := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierQ4
end
