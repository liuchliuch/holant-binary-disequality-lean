import Holant.Proofs.Closure.ClosureKleinCurrentCards

/-! Closed all-arity zero-safe standard/exotic canonical matching deck from
the literal CURRENT original-field raw deck. All ordered pairs, all residual
orders, all four dual labels and every zero card are covered. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain

theorem CanonicalMatching.scale {n : ℕ} {row : K.Kind} {f : Signature AlgebraicComplex n}
    (actual : CanonicalMatching row f) (c : AlgebraicComplex) (nonzero : c≠0) :
    CanonicalMatching row (c • f) := by
  rcases actual with zero | ⟨M,labels,scalar,factors,equation⟩
  · left;rw [zero,smul_zero]
  · let N : Presentation AlgebraicComplex (Fin n) := { M with scalar := c*M.scalar }
    refine Or.inr ⟨N,labels,mul_ne_zero nonzero scalar,factors,?_⟩
    calc
      _=c • M.tensor := congrArg (c • ·) equation
      _=N.tensor := by funext x;simp [N,Presentation.tensor,productValue,mul_assoc]

def OrderedMatchingDeck {n : ℕ} (row : K.Kind) (h : Signature AlgebraicComplex (n+2)) : Prop :=
  ∀ order : Equiv.Perm (Fin (n+2)),∀ k : Fin 4,
    CanonicalMatching row (Signature.contract (K.dual row k) (Tensor.reindex order.symm h))

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable {n : ℕ} (f : Signature (OI.K G) (n+2))

theorem normalizedCard_matching
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) :
    CanonicalMatching (kind G P torsion cardinal noncyclic)
      (canonicalCard G P torsion cardinal noncyclic f order k) := by
  have raw := matching_mapped G P torsion cardinal noncyclic _
    (stable _ (Or.inr ⟨cardKey G P torsion cardinal noncyclic order k,rfl⟩))
  have corrected := raw.scale
    (ClosureSourceRows.embedding G (dualCorrection G P torsion cardinal noncyclic k))⁻¹
    (inv_ne_zero ((map_ne_zero _).mpr (dualCorrection_nonzero G P torsion cardinal noncyclic k)))
  rw [rawCard_mapped,smul_smul,inv_mul_cancel₀
    ((map_ne_zero _).mpr (dualCorrection_nonzero G P torsion cardinal noncyclic k)),one_smul] at corrected
  exact corrected

/-- The source group producer and matching scalar transport close this deck
predicate internally from the actual source matching witnesses. No separate
canonical matching, fibre, atlas or classifier is supplied. -/
theorem ordered_matching_deck
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    OrderedMatchingDeck (kind G P torsion cardinal noncyclic)
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) :=
  normalizedCard_matching G P torsion cardinal noncyclic f stable

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
