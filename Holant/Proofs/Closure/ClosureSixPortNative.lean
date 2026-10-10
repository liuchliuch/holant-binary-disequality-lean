import Holant.Proofs.Closure.ClosureSixPortCurrentAlgebraicCard
import Holant.Proofs.Closure.ClosureSixPortUnary
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! NEW UNVERIFIED source-field consequences of the additive six-port core.
Coefficient mapping preserves primality by exact pivot-factor descent. This
uses no new field extraction or physical factor-access backend. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Tractable Holant.Algebraic Holant.Projective
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

/-- Support parity is already a consequence in the ORIGINAL field, rather
than a support restriction imposed only on its complex embedding. -/
theorem current_global_parity
    (N : ClosureMarkedDihedral.NativeM
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion)) (h : Signature (OI.K G) 6) (nonzero : h ≠ 0)
    (stable : ∀ g ∈ rawDeck P.family torsion h, MatchingOrZero (actualTransfers P.family) g) :
    ∃ p : ZMod 2, ∀ w, parity w ≠ p → h w = 0 := by
  have mappedNonzero : RH.mapSignature (sourceComplex G) h ≠ 0 := by
    intro hz
    apply nonzero
    funext w
    apply (sourceComplex G).injective
    simpa only [RH.mapSignature,Pi.zero_apply,map_zero] using congrFun hz w
  obtain ⟨p,hp⟩ := exists_global_parity N.range _ mappedNonzero
    (orderedRootDeck_of_current G P torsion N h stable)
  refine ⟨p,fun w hw => ?_⟩
  apply (sourceComplex G).injective
  simpa only [RH.mapSignature,Pi.zero_apply,map_zero] using hp w hw

/-- Exact coefficient descent reflects the complex non-prime conclusion. -/
theorem source_not_prime_of_complex (h : Signature (OI.K G) 6)
    (nonprime : ¬ Prime (⟨6,RH.mapSignature (sourceComplex G) h⟩ : AnySignature ℂ)) :
    ¬ Prime (⟨6,h⟩ : AnySignature (OI.K G)) := by
  intro hp
  apply nonprime
  exact (prime_mapSignature_iff (sourceComplex G) ⟨6,h⟩).mpr hp

/-- Both literal zero/proportional orientations descend to an ORIGINAL-field
proper split; no complex normalization factor is treated as a source gadget. -/
theorem current_zero_proportional_not_prime (h : Signature (OI.K G) 6)
    (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector (RH.mapSignature (sourceComplex G) h) e p)
    (dependent : DependentEndpoints
      (sliceSix (RH.mapSignature (sourceComplex G) h) e (!p) false)
      (sliceSix (RH.mapSignature (sourceComplex G) h) e (!p) true)) :
    ¬ Prime (⟨6,h⟩ : AnySignature (OI.K G)) :=
  source_not_prime_of_complex G h (zero_proportional_not_prime _ e p zero dependent)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
