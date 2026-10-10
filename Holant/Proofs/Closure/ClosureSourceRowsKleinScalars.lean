import Holant.Proofs.Closure.ClosureSourceRowsKlein

/-! Original-field output-card scalars for either literal Klein row. Every
coefficient is recovered from source entries; no foreign scale is treated as
a source-field constant or as a normalized gadget resource. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Marked
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (kind : EqualityQuaternary.Klein.Kind) (coverage : KleinCoverage G P torsion kind)

structure KleinLineSource (B : Binary (K:=OI.K G)) where
  index : Fin 4
  coefficient : OI.K G
  nonzero : coefficient ≠ 0
  literal : B = coefficient • (actualRepresentative P.family torsion
    (kleinIndex G P torsion kind coverage index).key : Binary (K:=OI.K G))

def kleinLineSource (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    KleinLineSource G P torsion kind coverage B := by
  let h := actual_binary_klein G P torsion kind coverage B hB
  let k := Classical.choose h
  let hs := Classical.choose_spec h
  let c := Classical.choose hs
  have hc := Classical.choose_spec hs
  let R := kleinIndex G P torsion kind coverage k
  let d := B (kleinPivot kind k).1 (kleinPivot kind k).2 / R.coefficient
  have hp : embedding G (B (kleinPivot kind k).1 (kleinPivot kind k).2) = c := by
    have hv := congrFun (congrFun hc.2 (kleinPivot kind k).1) (kleinPivot kind k).2
    change embedding G (B (kleinPivot kind k).1 (kleinPivot kind k).2) =
      c * EqualityQuaternary.Klein.E kind k (kleinPivot kind k).1 (kleinPivot kind k).2 at hv
    rw [klein_pivot_one,mul_one] at hv
    exact hv
  have hd : embedding G d = c / embedding G R.coefficient := by
    change embedding G (_ / _) = _
    rw [map_div₀,hp]
  have hR : embedding G R.coefficient ≠ 0 := (map_ne_zero (embedding G)).mpr R.nonzero
  have hd0 : d ≠ 0 := by
    apply (map_ne_zero (embedding G)).mp
    rw [hd]
    exact div_ne_zero hc.1 hR
  refine ⟨k,d,hd0,?_⟩
  funext a b
  apply (embedding G).injective
  change embedding G (B a b) = embedding G (d * actualRepresentative P.family torsion R.key a b)
  rw [map_mul,hd]
  have he := congrFun (congrFun hc.2 a) b
  have hr := congrFun (congrFun R.normal a) b
  change embedding G (B a b) = c * EqualityQuaternary.Klein.E kind k a b at he
  change embedding G (actualRepresentative P.family torsion R.key a b) =
    embedding G R.coefficient * EqualityQuaternary.Klein.E kind k a b at hr
  rw [he,hr]
  field_simp

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

theorem kleinLineSource_mapped (B : Binary (K:=OI.K G))
    (R : KleinLineSource G P torsion kind coverage B) :
    B.map (embedding G) = scale (embedding G R.coefficient)
      ((kleinRepresentatives G P torsion kind q core hcore coverage).matrix R.index) := by
  calc
    B.map (embedding G) = (R.coefficient • actualRepresentative P.family torsion
        (kleinIndex G P torsion kind coverage R.index).key).map (embedding G) :=
      congrArg (fun B : Binary (K:=OI.K G) => B.map (embedding G)) R.literal
    _ = _ := by
      funext a b
      exact map_mul (embedding G) R.coefficient
        (actualRepresentative P.family torsion (kleinIndex G P torsion kind coverage R.index).key a b)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
