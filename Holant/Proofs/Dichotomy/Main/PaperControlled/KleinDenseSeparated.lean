import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedActual
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinRealizedEq4
import Holant.Proofs.Closure.ClosureSourceRowsKleinNative

/-! The actual standard-Klein complete group supplies projective Pauli Z.
The separating dense-table branch constructs Eq4 and closes the whole original
current problem; no extra binary-resource or source theorem is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinDenseSeparated
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem coverage : ClosureSourceRows.KleinCoverage G P torsion .standard := by
  rw [←standard]
  exact ClosureSourceRows.nativeKleinResources G P torsion cardinal noncyclic

def representatives : Klein.Representatives (ClosureSourceRows.ambientFamily G P) .standard where
  matrix k := ClosureSourceRows.representative G P torsion
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).key
  multiplier k := ClosureSourceRows.embedding G
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).coefficient
  multiplier_ne_zero k := (map_ne_zero _).mpr
    (ClosureSourceRows.kleinIndex G P torsion .standard (coverage G P torsion cardinal noncyclic standard) k).nonzero
  actual _k := ClosureSourceRows.representative_actual G P torsion _
  normal_form k := (ClosureSourceRows.kleinIndex G P torsion .standard
    (coverage G P torsion cardinal noncyclic standard) k).normal

include torsion cardinal noncyclic standard in
theorem pauli_Z : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality
    (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)) := by
  let reps := representatives G P torsion cardinal noncyclic standard
  refine ⟨reps.multiplier 2,reps.multiplier_ne_zero 2,?_⟩
  have h := reps.actual 2
  rw [reps.normal_form] at h
  convert h using 1
  funext x
  congr 1
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Klein.E,Klein.basisQ,Klein.matrix,T.Z,h0,h1]

include torsion cardinal noncyclic standard in
theorem classified (a b c d : AlgebraicComplex)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality (T.normal a b c d))
    (separated : (a^2-b^2)^2≠(c^2-d^2)^2) :
    PaperControlled.KleinEq4Source.CurrentTract G P ∨
      PaperControlled.KleinEq4Source.Hard G :=
  PaperControlled.KleinRealizedEq4.classified G P
    (GlobalCloseCompletionKleinTwistedActual.normal_eq4 _ (StableDenseGaugeCurrent.ambient_identity G P)
      (pauli_Z G P torsion cardinal noncyclic standard) a b c d actual separated)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinDenseSeparated
end
