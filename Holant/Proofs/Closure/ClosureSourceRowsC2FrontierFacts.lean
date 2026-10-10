import Holant.Proofs.Closure.ClosureSourceRowsC2Physical
import Holant.Proofs.Closure.FrontierQ4
import Holant.Proofs.Closure.HistoryPalette

/-! A q4 occurrence's own batch adds only binary roots and prime leaves of
arity at most two. Every nonbinary label is literally old. Hence the actual
q4 minimum and global noOdd persist, without borrowing another core's deck. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.C2Frontier
open Holant Holant.Algebraic Holant.Tractable
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
section Generic
variable {L : Type*} [Field L] [NumberField L]

omit [NumberField L] in
theorem fullRoot_four_arity (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4) (k : FullDeckIndex F torsion q) :
    (fullDeckRoot F torsion q k).1.1 = 2 := by cases k <;> rfl

/-- Literal old membership, stronger than merely preserving odd predicates. -/
theorem nonbinary_old (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4) (g : AnySignature L) (hg : g ∈ fullRetainedDeck F torsion q)
    (hn : 3 ≤ g.1) : g ∈ F := by
  classical
  rcases hg with hold | hnew
  · exact hold
  · obtain ⟨k,_,hr | hl⟩ := (mem_batchCarrier (fullDeckUniverse F torsion q)
      (fullDeckRoot F torsion q) g).mp hnew
    · rw [hr,fullRoot_four_arity] at hn
      omega
    · have hb := (fullDeckRoot F torsion q k).2.leaf_arity_le g hl
      rw [fullRoot_four_arity] at hb
      omega

theorem noOdd_retained (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4)
    (noOdd : ∀ g ∈ F, Prime g → 3 ≤ g.1 → Even g.1) :
    ∀ g ∈ fullRetainedDeck F torsion q, Prime g → 3 ≤ g.1 → Even g.1 := by
  intro g hg hp hn
  exact noOdd g (nonbinary_old F torsion q g hg hn) hp hn

/-- A real old q4 minimum remains a real minimum in its own full batch. -/
def retainedCore (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4) (core : MinimumCore F) : MinimumCore (fullRetainedDeck F torsion q) where
  signature := core.signature
  retained := fullRetainedDeck_retains F torsion q core.retained
  prime := core.prime
  nonbinary := core.nonbinary
  minimum := fun g hg hp hn => core.minimum g (nonbinary_old F torsion q g hg hn) hp hn

end Generic

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

/-- Resetting the saved active occurrence is a new local batch; no strict
sourceOmega inequality is claimed merely for choosing a different q4 leaf. -/
def state : StabilizationMathematical.State (OI.K G) where
  family := P.family
  finite := Set.finite_range _
  equality := P.equality
  saturated := HistoryPalette.palette_saturated G P
  torsion := torsion
  core := core
  m := 2
  signature := q
  coreLiteral := hcore
  proper := by norm_num
  evenArity := ⟨2,rfl⟩

theorem minimum_arity : (state G P torsion q core hcore).minimum.signature.1 = 4 := by
  let C := state G P torsion q core hcore
  have hlo := (retainedCore P.family torsion q core).minimum C.minimum.signature
    C.minimum.retained C.minimum.prime C.minimum.nonbinary
  have hhi := C.minimum_nonincrease
  have hn : core.signature.1 = 4 := congrArg Sigma.fst hcore
  change core.signature.1 ≤ C.minimum.signature.1 at hlo
  change C.minimum.signature.1 ≤ core.signature.1 at hhi
  change C.minimum.signature.1 = 4
  omega

theorem augmented_noOdd
    (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1) :
    StabilizationMathematical.NoOdd (state G P torsion q core hcore).augmented :=
  noOdd_retained P.family torsion q noOdd

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows.C2Frontier
