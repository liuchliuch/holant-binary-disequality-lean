import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticCards
import Holant.Proofs.Closure.ClosureExoticEightSource
import Holant.Pauli.ExoticKlein.SixPortTheorem

/-! The actual exotic CURRENT six-port deck supplies the existing checked
physical six-port theorem. Its exact proper factor is descended to OI.K G,
closing the missing arity-six arm of the exotic stable-prime bound. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticSix
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Pauli.ExoticKlein
open GlobalCloseCompletionKleinExoticCards (ordered_physical)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false


variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)

include cardinal noncyclic exotic in
theorem current_original_split (f : Signature (OI.K G) 6) (nonzero : f≠0)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃u v : AnySignature (OI.K G),∃split : ProperSplit (⟨6,f⟩ : AnySignature (OI.K G)) u v,
      split.scale=1 := by
  let phi := ClosurePhysicalBridge.complexEmbedding G
  let fc := RingHomRealization.mapSignature phi f
  have live : fc≠0 := by
    intro zero
    apply nonzero
    funext x
    apply phi.injective
    simpa only [fc,RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using congrFun zero x
  have safe := ClosureKleinCurrent.current_exotic_ordered G P torsion cardinal noncyclic exotic f stable
  obtain ⟨m,n,hm,hn,ports,u,v,_hu,_hv,equation⟩ :=
    SixPort.six_port_has_proper_tensor_factor fc live (ordered_physical fc safe)
  let split : ProperSplit (mapSignature phi (⟨6,f⟩ : AnySignature (OI.K G))) ⟨m,u⟩ ⟨n,v⟩ :=
    { left_pos := hm
      right_pos := hn
      ports := ports
      scale := 1
      equation := by
        funext x
        change fc x=1*(u (fun i=>x (ports (.inl i)))*v (fun i=>x (ports (.inr i))))
        rw [one_mul]
        exact congrFun equation x }
  obtain ⟨u',v',original,_ports,unit⟩ := ClosureSixPort.exact_split_descent phi ⟨6,f⟩ nonzero split
  exact ⟨⟨m,u'⟩,⟨n,v'⟩,original,unit⟩

include cardinal noncyclic exotic in
theorem current_not_prime (f : Signature (OI.K G) 6)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G)))
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) : False := by
  obtain ⟨u,v,split,_⟩ := current_original_split G P torsion cardinal noncyclic exotic f prime.1 stable
  exact prime.2 ⟨u,v,⟨split⟩⟩

include cardinal noncyclic exotic in
theorem stable_prime_residual_eq_two {m : ℕ} (f : Signature (OI.K G) (m+2))
    (proper : 2≤m) (even : Even (m+2)) (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)))
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) : m=2 := by
  have upper := ClosureExoticFiberCounts.stable_prime_residual_le_four G P torsion cardinal noncyclic exotic f even prime stable
  by_contra notTwo
  have four : m=4 := by rcases even with ⟨k,hk⟩; omega
  subst m
  exact current_not_prime G P torsion cardinal noncyclic exotic f prime stable


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticSix
end
