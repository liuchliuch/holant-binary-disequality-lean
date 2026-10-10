import Holant.Proofs.Closure.HistorySectorNormalizedMarking

/-! Concrete SAME-basis q4 support atlas from the actual CURRENT prime core.
Nonzero status is proved through the original embedding and inverse action;
the frozen weighted atlas is then applied. No endpoint, LP or solver outcome
is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (U : InvertibleKernel) (q : Signature (OI.K G) 4)

def sectorCore : Signature Scalar 4 := U.symm.action
  (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)

theorem sectorCore_nonzero (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩) :
    sectorCore G U q ≠ 0 := by
  have hq : q ≠ 0 := by
    have h := core.prime.1
    rw [hcore] at h
    exact h
  intro hz
  have h := congrArg U.action hz
  change U.action (U.symm.action _) = U.action (0 : Signature Scalar 4) at h
  rw [U.action_symm_action,ClosureFactorTreeAction.action_zero] at h
  apply hq
  funext x
  apply (algebraicEmbedding G).injective
  exact (congrFun h x).trans (algebraicEmbedding G).map_zero.symm

theorem complexCore_nonzero (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩) :
    complexTensor (sectorCore G U q) ≠ 0 := by
  intro hz
  apply sectorCore_nonzero G P U q core hcore
  funext x
  apply ClosureMarkedDihedral.inclusion.injective
  exact (congrFun hz x).trans ClosureMarkedDihedral.inclusion.map_zero.symm

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (sameBasis : params.basis = U)

def HasComplementaryPair : Prop :=
  ∃ w : Word, sectorCore G U q w ≠ 0 ∧ sectorCore G U q (complement w) ≠ 0

theorem support_atlas (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
    (R : RootDeck G P torsion U N params sameBasis q) :
    ∃ (p : Bool) (selected : PairIndex → Bool), (∃ i, selected i = true) ∧
      ∀ w, complexTensor (sectorCore G U q) w ≠ 0 ↔ ∃ i, selected i = true ∧
        (w = representative p i ∨ w = complement (representative p i)) := by
  have hd : (delta params : ℂ) ≠ 0 := (map_ne_zero ClosureMarkedDihedral.inclusion).mpr (delta_ne_zero params)
  have hr : ((delta params : ℂ)^2)^N.m = 1 := by
    exact_mod_cast delta_root params
  exact support_atlas_of_samples (marked_range params) (delta params : ℂ) hd hr
    (complexTensor (sectorCore G U q)) (complexCore_nonzero G P U q core hcore) R.normalized

theorem complementary_pair (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
    (R : RootDeck G P torsion U N params sameBasis q) : HasComplementaryPair G U q := by
  obtain ⟨p,selected,⟨i,hi⟩,atlas⟩ := support_atlas G P U q torsion N params sameBasis core hcore R
  refine ⟨representative p i,?_,?_⟩
  · have h := (atlas (representative p i)).mpr ⟨i,hi,Or.inl rfl⟩
    intro hz
    apply h
    change ClosureMarkedDihedral.inclusion (sectorCore G U q (representative p i)) = 0
    rw [hz,map_zero]
  · have h := (atlas (complement (representative p i))).mpr ⟨i,hi,Or.inr rfl⟩
    intro hz
    apply h
    change ClosureMarkedDihedral.inclusion (sectorCore G U q (complement (representative p i))) = 0
    rw [hz,map_zero]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
