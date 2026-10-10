import Holant.Proofs.Closure.ClosureSourceRowsMonomial

/-! The output-card line multiplier is likewise recovered in the ORIGINAL
field. A foreign analytic scale is not assumed to be a source coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Marked Holant.Marked.SupportAtlas
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM (ClosureMarkedDihedral.Source.group (embedding G) P.family torsion))

theorem monomial_pivot (p : Bool) (t : Phase N.m) :
    representative G P torsion (monomialIndex G P torsion N p t).key p false =
      embedding G (monomialIndex G P torsion N p t).coefficient := by
  rw [(monomialIndex G P torsion N p t).normal]
  cases p <;> simp [EqualityQuaternary.standard,S,R,diagonalKernel,Kernel.mul_apply,
    Signature.disequality,scale]

structure MonomialLineSource (B : Binary (K:=OI.K G)) where
  orientation : Bool
  phase : Phase N.m
  coefficient : OI.K G
  nonzero : coefficient ≠ 0
  literal : B = coefficient • actualRepresentative P.family torsion
    (monomialIndex G P torsion N orientation phase).key

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

def monomialLineSource (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    MonomialLineSource G P torsion N B := by
  let h := actual_monomial_line G P torsion N q core hcore B hB
  let p := Classical.choose h
  let hp := Classical.choose_spec h
  let t := Classical.choose hp
  let ht := Classical.choose_spec hp
  let ambientScale := Classical.choose ht
  have hambientScale := Classical.choose_spec ht
  let R := monomialIndex G P torsion N p t
  let d := B p false / R.coefficient
  have hd : embedding G d = ambientScale := by
    have he := congrFun (congrFun hambientScale.2 p) false
    change embedding G (B p false) = ambientScale * representative G P torsion R.key p false at he
    rw [monomial_pivot G P torsion N p t] at he
    change embedding G (B p false / R.coefficient) = ambientScale
    rw [map_div₀,he,mul_div_cancel_right₀]
    exact (map_ne_zero (embedding G)).mpr R.nonzero
  have hd0 : d ≠ 0 := by
    apply (map_ne_zero (embedding G)).mp
    rw [hd]
    exact hambientScale.1
  refine ⟨p,t,d,hd0,?_⟩
  funext a b
  apply (embedding G).injective
  change embedding G (B a b) = embedding G (d * actualRepresentative P.family torsion R.key a b)
  rw [map_mul,hd]
  exact congrFun (congrFun hambientScale.2 a) b

/-- The actual row line, with the recorded multiplier visibly in OI.K G. -/
theorem monomialLineSource_mapped (B : Binary (K:=OI.K G))
    (R : MonomialLineSource G P torsion N B) :
    B.map (embedding G) = scale (embedding G R.coefficient)
      ((monomialRepresentatives G P torsion N q core hcore).matrix R.orientation R.phase) := by
  calc
    B.map (embedding G) = (R.coefficient • actualRepresentative P.family torsion
        (monomialIndex G P torsion N R.orientation R.phase).key).map (embedding G) :=
      congrArg (fun B : Binary (K:=OI.K G) => B.map (embedding G)) R.literal
    _ = _ := by
      funext a b
      exact map_mul (embedding G) R.coefficient
        (actualRepresentative P.family torsion (monomialIndex G P torsion N R.orientation R.phase).key a b)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
