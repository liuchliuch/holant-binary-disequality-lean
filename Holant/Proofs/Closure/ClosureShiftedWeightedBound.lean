import Holant.Proofs.Closure.ClosureShiftedWeightedSelected
import Holant.Proofs.Closure.ClosureWeightedPencilSelected

/-! Closed even-prime arity≤4 in the actual shifted-A CURRENT source branch.
The higher anchored split and genuine weighted six-port Base split are both
constructed from the same original palette and guards. -/
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
variable (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
  Subgroup.centralizer ({Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.xClass} : Set (PGL2 ℂ)))
variable (noncyclic : ¬IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
variable (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
variable (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
variable (noZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass ∉
  ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)

include axis noncyclic notTwo notFour noZ in
/-- Every even source prime with a stable CURRENT rawDeck in the actual
shifted-A branch has arity at most four. No weighted-domain or six-port
closure certificate is supplied. -/
theorem selected_even_prime_arity_four {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (even : Even (n+2)) (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) : n+2 ≤ 4 := by
  have bound := selected_even_prime_arity_bound G P torsion axis noncyclic notTwo notFour noZ f stable even prime
  by_contra larger
  obtain ⟨k,hk⟩ := even
  have arity : n = 4 := by omega
  subst n
  exact ClosureWeightedPencil.selected_current_six_not_prime G P torsion axis noncyclic notTwo notFour noZ
    f prime.1 stable prime

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
