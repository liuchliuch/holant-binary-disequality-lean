import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralCurrent
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralHigherCurrent

/-! Every actually prepared stable current minimum excludes the semantic I
marking. Arity four and all higher even arities use the corresponding proved
coefficient producers, with the same literal current tensor throughout. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.StableCurrent
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)

theorem semantic_current_impossible {m : ℕ} (f : Signature (OI.K G) (m+2))
    (proper : 2≤m) (even : Even (m+2)) (core : MinimumCore P.family)
    (same : core.signature=⟨m+2,f⟩)
    (stable : ∀q∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) q)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .icosahedral)) : False := by
  by_cases hm : m=2
  · subst m
    exact semantic_icosahedral_impossible G P torsion f core same stable semantic
  · have high : 6≤m+2 := by obtain ⟨k,hk⟩ := even;omega
    have hp : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := same ▸ core.prime
    exact HigherCurrent.semantic_prime_high_impossible (ClosureSourceRows.embedding G) P.family torsion
      f high stable hp P.equality semantic

theorem prepared_core_impossible (core : MinimumCore P.family)
    (deck : GroupPreparedStability.PreparedDeck G P torsion core)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .icosahedral)) : False :=
  semantic_current_impossible G P torsion deck.signature deck.proper deck.even core
    deck.literal deck.matching semantic


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.StableCurrent
end
