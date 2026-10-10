import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseSource
import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedEOModel

/-! Sparse q4 models preserve the actual one-q/literal-I physical graph and
reflect its selected EO class to the original row. These join binary models
in one mixed source; no independent singleton class is selected. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseModel
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome
open GlobalCloseCompletionMixedEOModel
namespace S
export GlobalCloseCompletionSparseSource (graph labels uses table table_exact nonzero)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Fin t → Signature (OI.K G) 4) (core : Fin t → MinimumCore P.family)
variable (literal : ∀i,(core i).signature=⟨4,q i⟩)
variable (stable : ∀i,∀f∈rawDeck P.family torsion (q i),MatchingOrZero (actualTransfers P.family) f)
variable (d : ∀i,SparseOutput G P (q i) (core i) (literal i))

theorem graph_exact (i : Fin t) : (S.graph G P q core literal d i).denote=
    eoRow G P (q i) (core i) (literal i) (d i) :=
  (Flip.denote (embedded G (q i)) (d i).mask).trans (eoRow_exact G P (q i) (core i) (literal i) (d i)).symm

def model (i : Fin t) : Model G P ⟨4,embedded G (q i)⟩ where
  graph := S.graph G P q core literal d i
  labels := S.labels G P q core literal d i
  exact := GlobalCloseCompletionMacroFamily.labels_exact G P (S.graph G P q core literal d i)
    (S.uses G P q core literal d i)
  native := Flip.native (embedded G (q i)) (d i).mask
  positive := by change 0<4; decide
  nonzero := by
    rw [graph_exact]
    have hn := S.nonzero G P q core literal d i
    rw [S.table_exact] at hn
    exact hn
  central := by
    rw [graph_exact]
    intro x hx
    change 2*weight x≠4 at hx
    apply eoRow_support G P (q i) (core i) (literal i) (d i) x
    omega
  reconstruct := by
    intro sign C hs hp
    rw [graph_exact] at hs hp
    have h := GlobalCloseCompletionSparseFamily.class_of_supports
      (eoRow G P (q i) (core i) (literal i) (d i))
      (eoRow_support G P (q i) (core i) (literal i) (d i))
      (StableCurrentEvenEOTract.eoRow_complement_closed G P torsion N
        (q i) (core i) (literal i) (stable i) (d i)) sign C hs hp
    rw [eoRow_exact] at h
    exact StableCurrentEvenEOTract.class_unflip C (embedded G (q i)) (d i).mask h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseModel
end
