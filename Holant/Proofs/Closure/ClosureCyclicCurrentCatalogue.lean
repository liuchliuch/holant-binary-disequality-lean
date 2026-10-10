import Holant.Proofs.Closure.ClosureCyclicCurrentCards

/-! Exact original-key/card provenance and physical original-G phase/card
access. Every phase uses its SAME source representative key and pivot, and
all ordered physical cards use the literal no-dressing CURRENT raw key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (τ : ResidualTorsion P.family)
variable (N : C.NativeCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
variable (t : Physical.Root N.m)

def phaseOriginal : Binary (K:=OI.K G) :=
  actualRepresentative P.family τ (phaseIndex (ClosureSourceRows.embedding G) P.family τ N t).key

def phaseAccess : CurrentSignatureAccess G P ⟨2,binarySignature (phaseOriginal G P τ N t)⟩ :=
  currentSignatureAccess G P _ (actualRepresentative_actual P.family τ
    (phaseIndex (ClosureSourceRows.embedding G) P.family τ N t).key).1

@[simp] theorem phaseAccess_controlled : (phaseAccess G P τ N t).toOriginal.controlled =
    RetainedBranch.controlledToOriginal G P ⟨2,binarySignature (phaseOriginal G P τ N t)⟩
      (phaseAccess G P τ N t).power := rfl
@[simp] theorem phaseAccess_reverse_controlled : (phaseAccess G P τ N t).fromOriginal.controlled =
    RetainedBranch.controlledFromOriginal G P ⟨2,binarySignature (phaseOriginal G P τ N t)⟩ := rfl

variable (q : Signature (OI.K G) 4)
def cardKey (i : Fin 3) (side order : Bool) : RawCardKey 2 (completeGroup P.family τ) :=
  ClosureSourceRows.orderedKey P.family τ (ClosureSourceRows.pairPermutation i side order)
    (phaseIndex (ClosureSourceRows.embedding G) P.family τ N t).key

/-- Exact matrix equality before Walsh action or projective division. -/
theorem card_raw_exact (i : Fin 3) (side order : Bool) :
    Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) i side order
      ((representatives (ClosureSourceRows.embedding G) P.family τ N).matrix t) =
    (binaryMatrix (rawCard P.family τ q (cardKey G P τ N t i side order))).map
      (ClosureSourceRows.embedding G) := by
  rw [← ClosureSourceRows.pairPermutation_card]
  exact ClosureSourceRows.sourceCard_raw G P τ q _ _

theorem card_in_current_deck (i : Fin 3) (side order : Bool) :
    rawCard P.family τ q (cardKey G P τ N t i side order) ∈ rawDeck P.family τ q :=
  Or.inr ⟨cardKey G P τ N t i side order,rfl⟩

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
def cardAccess (i : Fin 3) (side order : Bool) : CurrentSignatureAccess G P
    ⟨2,rawCard P.family τ q (cardKey G P τ N t i side order)⟩ :=
  ClosureSourceRows.orderedCardAccess G P τ q core hcore _ _

@[simp] theorem cardAccess_controlled (i : Fin 3) (side order : Bool) :
    (cardAccess G P τ N t q core hcore i side order).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P _
        (cardAccess G P τ N t q core hcore i side order).power := rfl
@[simp] theorem cardAccess_reverse_controlled (i : Fin 3) (side order : Bool) :
    (cardAccess G P τ N t q core hcore i side order).fromOriginal.controlled =
      RetainedBranch.controlledFromOriginal G P _ := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
