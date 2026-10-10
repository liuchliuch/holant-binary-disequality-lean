import Holant.Proofs.Closure.ClosureSixPortCurrentCards
import Holant.Dihedral.CompatibleClosure.Monomial

/-! NEW UNVERIFIED algebraic normalized card transport with an ORIGINAL-field
scalar recovered from the actual sandwiched matrix entry. The all-arity phase
kernel is exactly the frozen CompatibleClosure.M convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Tractable Holant.Algebraic Holant.Projective Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked Holant.Marked.SupportAtlas

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

def rootComplex (t : Phase N.m) : (t.val : ℂ)^N.m=1 := by exact_mod_cast t.property

def algebraicCardIndex (p : Bool) (t : Phase N.m) :=
  cardIndex G P torsion N p (t.val : ℂ) (rootComplex G P torsion N t)

/-- This pivot is literally in the SAME original coefficient field. -/
def algebraicCardCoefficient (p : Bool) (t : Phase N.m) : OI.K G :=
  actualRepresentative P.family torsion (algebraicCardIndex G P torsion N p t).key true (!p)

theorem algebraicCardCoefficient_complex (p : Bool) (t : Phase N.m) :
    sourceComplex G (algebraicCardCoefficient G P torsion N p t) =
      cardScalar G P torsion N p (t.val : ℂ) (rootComplex G P torsion N t) := by
  have hk := congrFun (congrFun
    (cardKernel_exact G P torsion N p (t.val : ℂ) (rootComplex G P torsion N t)) false) p
  simpa only [Matrix.map_apply,matrix_Xsandwich,Bool.not_false,
    Pi.smul_apply,smul_eq_mul,algebraicCardCoefficient,algebraicCardIndex,
    Holant.Dihedral.EndpointParallelogram.phaseKernel,Bool.false_xor,Bool.false_eq_true,ite_true,ite_false,mul_one] using hk

theorem algebraicCardCoefficient_nonzero (p : Bool) (t : Phase N.m) :
    algebraicCardCoefficient G P torsion N p t ≠ 0 := by
  apply (map_ne_zero (sourceComplex G)).mp
  rw [algebraicCardCoefficient_complex]
  exact cardScalar_nonzero G P torsion N p _ _

theorem compatibleM_complex (p : Bool) (t : Scalar) :
    complexMatrix (Holant.Dihedral.CompatibleClosure.M p t) =
      Holant.Dihedral.EndpointParallelogram.phaseKernel p (t : ℂ) := by
  funext u v
  cases p <;> cases u <;> cases v <;>
    simp [complexMatrix,Holant.Dihedral.CompatibleClosure.M,
      Holant.Marked.monomial,Holant.Dihedral.EndpointParallelogram.phaseKernel]

/-- Exact ORIGINAL scalar times the frozen algebraic phase kernel. -/
theorem algebraicCardKernel_exact (p : Bool) (t : Phase N.m) :
    (X * actualRepresentative P.family torsion (algebraicCardIndex G P torsion N p t).key * X).map
      (ClosureSourceRows.embedding G) =
      ClosureSourceRows.embedding G (algebraicCardCoefficient G P torsion N p t) •
        Holant.Dihedral.CompatibleClosure.M p t.val := by
  have hk := cardKernel_exact G P torsion N p (t.val : ℂ) (rootComplex G P torsion N t)
  rw [←algebraicCardCoefficient_complex] at hk
  funext u v
  apply CyclicBoundary.AlgebraicRepresentatives.inclusion.injective
  have he := congrFun (congrFun hk u) v
  have hM := congrFun (congrFun (compatibleM_complex p t.val) u) v
  simp only [Matrix.map_apply,Pi.smul_apply,smul_eq_mul] at he ⊢
  rw [←hM] at he
  exact he

/-- All ordered actual raw cards map to the SAME frozen algebraic contraction
with a nonzero scalar from the ORIGINAL field and the SAME literal raw key. -/
theorem ordered_algebraic_card_raw_scalar {n : ℕ} (h : Signature (OI.K G) (n+2))
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.m) :
    RH.mapSignature (ClosureSourceRows.embedding G)
      (rawCard P.family torsion h (DeckContraction.orderedKey P.family torsion e
        (algebraicCardIndex G P torsion N p t).key)) =
      ClosureSourceRows.embedding G (algebraicCardCoefficient G P torsion N p t) •
        Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
          (Tensor.reindex e.symm (RH.mapSignature (ClosureSourceRows.embedding G) h)) := by
  rw [DeckContraction.rawCard_ordered]
  have kernel := algebraicCardKernel_exact G P torsion N p t
  funext x
  simp only [RH.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  have hk := congrFun (congrFun kernel u) v
  simp only [Matrix.map_apply,Pi.smul_apply,smul_eq_mul] at hk
  rw [hk]
  ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
