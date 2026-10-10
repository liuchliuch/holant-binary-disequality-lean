import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterResources
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardMatchingAffine

/-! The actual standard-Pauli current group supplies all four Bell resources
required by the signed Radon programme. Original representative multipliers
are retained; no normalized Bell row is inserted as a free vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCurrentResources
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell map_bell)
end C
namespace K
export Holant.Certificates.EqualityQuaternary.Klein (E basisQ matrix embed_apply)
end K
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def index (d l : ZMod 2) : Fin 4 := if d=0 then (if l=0 then 0 else 2) else (if l=0 then 1 else 3)

theorem bell_canonical (d l : ZMod 2) : Holant.ReedMuller.TwoChart.algebraicBell d l=
    kernelSignature (K.E .standard (index d l)) := by
  funext x
  fin_cases d <;> fin_cases l <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Holant.ReedMuller.TwoChart.algebraicBell,bellSignature,bellKernel,parityKernel,
      sign,intSign,bit,boolEquiv,index,kernelSignature,K.E,K.basisQ,K.matrix,
      K.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,h0,h1]
  all_goals exact Subtype.ext rfl

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic in
theorem row_actual (k : Fin 4) : Gadget.RealizesUpTo P.family .disequality
    (ClosureKleinCurrent.rowTable G P torsion cardinal noncyclic k) := by
  let J := ClosureKleinCurrent.index G P torsion cardinal noncyclic k
  refine ⟨J.coefficient,J.nonzero,?_⟩
  convert (actualRepresentative_actual P.family torsion J.key).1 using 1
  funext x
  change J.coefficient*(J.coefficient⁻¹*actualRepresentative P.family torsion J.key (x 0) (x 1))=_
  rw [←mul_assoc,mul_inv_cancel₀ J.nonzero,one_mul]
  rfl

include cardinal noncyclic standard in
theorem bell_actual (d l : ZMod 2) : Gadget.RealizesUpTo P.family .disequality (C.bell d l) := by
  have row : ClosureKleinCurrent.rowTable G P torsion cardinal noncyclic (index d l)=C.bell d l := by
    funext x
    apply (ClosureSourceRows.embedding G).injective
    have mapped := ClosureKleinCurrent.rowTable_mapped G P torsion cardinal noncyclic (index d l)
    rw [standard,←bell_canonical,←C.map_bell (ClosureSourceRows.embedding G)] at mapped
    exact congrFun mapped x
  rw [←row]
  exact row_actual G P torsion cardinal noncyclic (index d l)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCurrentResources
end
