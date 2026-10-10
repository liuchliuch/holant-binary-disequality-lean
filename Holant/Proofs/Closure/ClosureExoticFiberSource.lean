import Holant.Proofs.Closure.ClosureExoticFiberFull
import Holant.Proofs.Closure.ClosureKleinCurrentExotic
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! The complete exotic fibre is derived from the SAME actual CURRENT raw deck
and the original-field prime. Complex primality is the proved field-descent
criterion; no new no-factor or fibre-selection argument is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
open Holant Holant.Tractable Holant.Algebraic
open Holant.Pauli.ExoticKlein
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure

/-- The explicit exact tensor factor is a proper split with scale1 and the
SAME physical port bijection; prime excludes it. -/
theorem prime_no_tensor_factor {n : ℕ} (f : Signature ℂ n)
    (prime : Prime (⟨n,f⟩ : AnySignature ℂ)) : ¬ Fiber.HasProperTensorFactor f := by
  rintro ⟨a,b,ha,hb,ports,u,v,hu,hv,he⟩
  apply prime.2
  refine ⟨⟨a,u⟩,⟨b,v⟩,⟨{left_pos:=ha,right_pos:=hb,ports:=ports,scale:=1,equation:=?_}⟩⟩
  funext x
  have hx := congrFun he x
  simpa only [Tensor.reindex,Tensor.tensor,Units.val_one,one_mul] using hx

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- Closed original-field prime/current-group source for all four live rows
and full label permutations. Every scalar in the output fibre is analytic ℂ;
no claim that it is an additional source gadget or original coefficient is made. -/
theorem current_prime_full_fiber (P : Palette G) (torsion : ResidualTorsion P.family)
    (cardinal : Nat.card (completeGroup P.family torsion)=4)
    (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
    (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)
    (r : ℕ) (positive : 0<r) (f : Signature (OI.K G) (2*r+6))
    (prime : Prime (⟨2*r+6,f⟩ : AnySignature (OI.K G)))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ t : ℕ, ∃ M : Matching (Fin (2*r+6)) (t+1),
      ∃ weight : Label → ℂ, ∃ labels : Label → Fin (t+1) → Label,
        (∀ k,labels k 0=k) ∧
        RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
          Fiber.tensor M weight labels ∧
        (∀ k,weight k≠0) ∧
        (∀ e,Function.Bijective (fun k => labels k e)) ∧3≤t := by
  have hp := (prime_mapSignature_iff (ClosurePhysicalBridge.complexEmbedding G)
    (⟨2*r+6,f⟩ : AnySignature (OI.K G))).mpr prime
  have primeComplex : Prime (⟨2*r+6,
      RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f⟩ : AnySignature ℂ) := hp
  exact common_full_permutation_fiber r positive _ primeComplex.1
    (ClosureKleinCurrent.current_exotic_ordered G P torsion cardinal noncyclic exotic f stable)
    (prime_no_tensor_factor _ primeComplex)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
