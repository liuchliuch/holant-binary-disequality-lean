import Holant.Proofs.Closure.ClosureSourceRowsMatching

/-! Exact source resources for a literal native Klein row. This intermediate
coverage predicate concerns only the finite ACTUAL representative catalogue.
The actual order-four group-shape producer supplies it; it is not a classifier,
SourceDeck or future compiler completing the global task. Every multiplier is
recovered at a unit pivot in the original field before physical retention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.Marked
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (kind : EqualityQuaternary.Klein.Kind)

structure KleinCoverage : Prop where
  forward : ∀ j : completeGroup P.family torsion,
    representative G P torsion j ∈ EqualityQuaternary.Klein.group kind
  backward : ∀ k : Fin 4, ∃ j : completeGroup P.family torsion,
    ∃ c : Scalar, c ≠ 0 ∧ representative G P torsion j = scale c (EqualityQuaternary.Klein.E kind k)

def kleinPivot (k : Fin 4) : Bool × Bool :=
  (false,if k=0 ∨ (kind=.standard ∧ k=2) then false else true)

theorem klein_pivot_one (k : Fin 4) :
    EqualityQuaternary.Klein.E kind k (kleinPivot kind k).1 (kleinPivot kind k).2 = 1 := by
  cases kind <;> fin_cases k <;>
    simp [kleinPivot,EqualityQuaternary.Klein.E,EqualityQuaternary.Klein.basisQ,
      EqualityQuaternary.Klein.matrix]

structure KleinIndex (k : Fin 4) where
  key : completeGroup P.family torsion
  coefficient : OI.K G
  nonzero : coefficient ≠ 0
  normal : representative G P torsion key = scale (embedding G coefficient) (EqualityQuaternary.Klein.E kind k)

def kleinIndex (coverage : KleinCoverage G P torsion kind) (k : Fin 4) : KleinIndex G P torsion kind k := by
  let h := coverage.backward k
  let j := Classical.choose h
  let hs := Classical.choose_spec h
  let c := Classical.choose hs
  have hc := Classical.choose_spec hs
  let d := actualRepresentative P.family torsion j (kleinPivot kind k).1 (kleinPivot kind k).2
  have hd : embedding G d = c := by
    have hv := congrFun (congrFun hc.2 (kleinPivot kind k).1) (kleinPivot kind k).2
    simpa only [representative,Matrix.map_apply,scale,klein_pivot_one,mul_one] using hv
  have hd0 : d ≠ 0 := by
    apply (map_ne_zero (embedding G)).mp
    rw [hd]
    exact hc.1
  exact ⟨j,d,hd0,by rw [hd]; exact hc.2⟩

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

def kleinRepresentatives (coverage : KleinCoverage G P torsion kind) : EqualityQuaternary.Klein.Representatives
    (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num))) kind where
  matrix := fun k => representative G P torsion (kleinIndex G P torsion kind coverage k).key
  multiplier := fun k => embedding G (kleinIndex G P torsion kind coverage k).coefficient
  multiplier_ne_zero := fun k => (map_ne_zero (embedding G)).mpr (kleinIndex G P torsion kind coverage k).nonzero
  actual := fun k => Gadget.realizes_of_mem _ .disequality _
    (representative_ambient_retained G P torsion q core hcore (by norm_num)
      (kleinIndex G P torsion kind coverage k).key)
  normal_form := fun k => (kleinIndex G P torsion kind coverage k).normal

theorem klein_retained (coverage : KleinCoverage G P torsion kind) :
    EqualityQuaternary.Klein.Retained (kleinRepresentatives G P torsion kind q core hcore coverage) :=
  fun k => representative_ambient_retained G P torsion q core hcore (by norm_num)
    (kleinIndex G P torsion kind coverage k).key

/-- Complete current-source actuality is reduced to its fixed representative,
then the literal row coverage is applied with both exact nonzero scales. -/
theorem actual_binary_klein (coverage : KleinCoverage G P torsion kind)
    (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    B.map (embedding G) ∈ EqualityQuaternary.Klein.group kind := by
  obtain ⟨j,c,hc,he⟩ := actual_binary_eq_representative P.family torsion B hB
  obtain ⟨k,d,hd,hm⟩ := coverage.forward j
  refine ⟨k,embedding G c*d,mul_ne_zero ((map_ne_zero (embedding G)).mpr hc) hd,?_⟩
  rw [he,Matrix.map_smul' (embedding G) c _ (embedding G).map_mul]
  change (embedding G c) • representative G P torsion j = _
  rw [hm]
  funext a b
  simp only [scale,Pi.smul_apply,smul_eq_mul,mul_assoc]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
