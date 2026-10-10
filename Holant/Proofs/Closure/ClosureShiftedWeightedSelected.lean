import Holant.Proofs.Closure.ClosureShiftedWeightedCurrent

/-! Actual-guard selected higher shifted-A source split and finite even-prime
arity bound. All coordinates/phase keys and the live matching anchor are
constructed internally from the same current palette and source. -/
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

/-- No supplied conjugator, model, weighted deck, gauge, anchor or split is
needed. The exact original selected factor and partition are returned. -/
theorem selected_original_split_of_nonzero {r : ℕ} (f : Signature (OI.K G) (2*r+4))
    (order : Equiv.Perm (Fin (2*r+4)))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (nonzero : f ≠ 0) (large : 2 ≤ r) :
    let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
    let N := Q.selected axis notTwo notFour
    let params := Q.parameters P.equality axis notTwo notFour noZ
    let receipt := nonzeroAnchorReceipt G P torsion Q.basis N params f order rfl (by trivial) stable
      (by omega) ⟨r+1,by omega⟩ nonzero
    ∃ e : Fin (r+1),∃ R : Signature (OI.K G) (2*r+2),∃ S : ProperSplit
      (⟨2*r+4,f⟩ : AnySignature (OI.K G))
      ⟨2,anchorOriginalTable G P torsion Q.basis N params f order receipt.source e⟩ ⟨2*r+2,R⟩,
      S.ports = (fixedPorts G P torsion Q.basis N params f order receipt.source rfl (by trivial) stable large e).trans order ∧
      S.scale = 1 := by
  dsimp only
  let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
  exact current_original_split_of_nonzero G P torsion Q.basis (Q.selected axis notTwo notFour)
    (Q.parameters P.equality axis notTwo notFour noZ) rfl (by trivial) f order stable nonzero large

include axis noncyclic notTwo notFour noZ in
/-- An even prime with a genuinely stable CURRENT raw deck in the actual
shifted-A branch has arity at most six. No minimum-core or six-port premise
is used, and the six-port case remains an explicit later boundary. -/
theorem selected_even_prime_arity_bound {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (even : Even (n+2)) (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) : n+2 ≤ 6 := by
  by_contra larger
  obtain ⟨k,hk⟩ := even
  have arity : n = 2*(k-2)+2 := by omega
  have range : 2 ≤ k-2 := by omega
  subst n
  exact selected_shifted_not_prime G P torsion f (Equiv.refl _) stable axis noncyclic notTwo notFour noZ range prime

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
