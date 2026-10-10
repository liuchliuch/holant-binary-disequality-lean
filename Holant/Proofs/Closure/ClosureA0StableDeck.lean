import Holant.Proofs.Closure.ClosureA0StableCards
import Holant.Proofs.Closure.ClosureCompatibleAlignmentParity

/-! Constructed all-arity standard-M root deck of the actual A0 ancestor.
The changed edge is kept; every sample is the coordinate image of a literal
CURRENT raw key with its nonzero scalar. Zero samples remain explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))

abbrev transformed {n : ℕ} (f : Signature (OI.K G) n) : Signature Scalar n :=
  basis.symm.action (RH.mapSignature (algebraicEmbedding G) f)

def rootCard {n : ℕ} (f : Signature (OI.K G) (n+2))
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) : Signature Scalar n :=
  Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
    (Tensor.reindex order.symm (transformed G f))

theorem algebraic_matching_smul {n m : ℕ} {q : Signature Scalar n}
    (matching : ClosureSixPort.AlgebraicRootMatching m q) (c : Scalar) (nonzero : c≠0) :
    ClosureSixPort.AlgebraicRootMatching m (c • q) := by
  obtain ⟨M,member,scalar,equation⟩ := matching
  let Q : Presentation Scalar (Fin n) := { M with scalar := c*M.scalar }
  refine ⟨Q,member,mul_ne_zero nonzero scalar,?_⟩
  rw [equation]
  funext x
  change c*(M.scalar * _)=(c*M.scalar)*_
  ring

theorem algebraic_matching_unscale {n m : ℕ} (q : Signature Scalar n) (c : Scalar) (nonzero : c≠0)
    (matching : c • q=0 ∨ ClosureSixPort.AlgebraicRootMatching m (c • q)) :
    q=0 ∨ ClosureSixPort.AlgebraicRootMatching m q := by
  rcases matching with zero | matching
  · exact Or.inl ((smul_eq_zero.mp zero).resolve_left nonzero)
  · right
    have h := algebraic_matching_smul matching c⁻¹ (inv_ne_zero nonzero)
    simpa only [smul_smul,inv_mul_cancel₀ nonzero,one_smul] using h

/-- The complete proper root deck is derived from current raw stability,
with the original deleted pair and every residual port order unchanged. -/
theorem rootCard_cases {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) :
    rootCard G P torsion N f order p t=0 ∨
      ClosureSixPort.AlgebraicRootMatching N.selected.m (rootCard G P torsion N f order p t) := by
  let key := DeckContraction.orderedKey P.family torsion order (index G P torsion N p t).key
  have h := matching_algebraic G P torsion N (rawCard P.family torsion f key)
    (stable _ (Or.inr ⟨key,rfl⟩))
  rw [ordered_card_raw_scalar G P torsion N f order p t] at h
  exact algebraic_matching_unscale _ _ (cardScalar_nonzero G P torsion N p t) h

/-- Map of the same ordered standard kernel, rather than a fresh root or
representative choice. -/
theorem rootCard_complex {n : ℕ} (f : Signature (OI.K G) (n+2))
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) :
    RH.mapSignature ClosureMarkedDihedral.inclusion (rootCard G P torsion N f order p t) =
      ClosureCompatibleAlignment.phaseCardN
        (RH.mapSignature ClosureMarkedDihedral.inclusion (transformed G f)) order p (t.val : ℂ) := by
  rw [ClosureCompatibleAlignment.phaseCardN_actual]
  funext x
  simp only [rootCard,RH.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
    Holant.Dihedral.EndpointParallelogram.card]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  have h := congrFun (congrFun (ClosureSixPort.compatibleM_complex p t.val) u) v
  simp only [Holant.Marked.SupportAtlas.complexMatrix] at h
  change ClosureMarkedDihedral.inclusion (Holant.Dihedral.CompatibleClosure.M p t.val u v)=
    Holant.Dihedral.EndpointParallelogram.phaseKernel p (t.val : ℂ) u v at h
  rw [h,one_mul]

/-- Full zero-safe complex root deck, selected from the actual A0 group.
The only closure input is the literal CURRENT raw deck. -/
theorem ordered_root_deck {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g) :
    ClosureCompatibleAlignment.OrderedRootDeckN N.selected.m
      (RH.mapSignature ClosureMarkedDihedral.inclusion (transformed G f)) := by
  intro order p t root
  let lifted : Phase N.selected.m :=
    CyclicBoundary.AlgebraicRepresentatives.liftRoot (by have := N.range; omega) ⟨t,root⟩
  have h := algebraic_matching_complex (by have := N.range; omega) _
    (rootCard_cases G P torsion N f stable order p lifted)
  rw [rootCard_complex] at h
  exact h

/-- The same derivation handles every outside closure of one reindexed
ancestor. No stability of an independently regenerated deck is supplied. -/
theorem outside_root_cases {r : ℕ} (f : Signature (OI.K G) (2*r+4))
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (original : Equiv.Perm (Fin (2*r+4))) (cut : Equiv.Perm (Fin (2*r+2)))
    (p : Bool) (t : Phase N.selected.m) :
    Holant.Dihedral.TwoCardLocalization.outsideClose cut (Holant.Dihedral.CompatibleClosure.M p t.val)
      (Tensor.reindex original.symm (transformed G f))=0 ∨
    ClosureSixPort.AlgebraicRootMatching N.selected.m
      (Holant.Dihedral.TwoCardLocalization.outsideClose cut (Holant.Dihedral.CompatibleClosure.M p t.val)
        (Tensor.reindex original.symm (transformed G f))) :=
  rootCard_cases G P torsion N f stable
    ((Holant.Dihedral.TwoCardLocalization.outsideOrder cut).trans original) p t

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
