import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientFilter
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTripleData
import Holant.Certificates.PlatonicIncidence.DomainCounts
import Mathlib.Data.Finset.Sort

/-! Coefficient extraction from the preserved marked-octahedral proof. Exact arithmetic on the OLD 122 O secants and their
OLD canonical endpoint indices. No matrix-atlas candidate, external data,
normal form or callback is supplied. Marked rows are evaluated in the same
existing Q(sqrt2,i) arithmetic; this is not a physical conjugation. -/
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped Matrix

/-- The literal endpoints used by the original globalLine_semantics proof. -/
def canonicalPair (t : Fin 122) : PairCode :=
  let v := globalWitness .octahedral t
  ![v.1,productIndex .octahedral v.1 (baseAnchor .octahedral v.2)]

theorem canonicalPair_ne (t : Fin 122) : canonicalPair t 0 ≠ canonicalPair t 1 :=
  translated_endpoints_ne .octahedral (globalWitness .octahedral t).1
    (globalWitness .octahedral t).2

theorem canonicalPair_mem : ∀ t : Fin 122,∀ i : Fin 2,
    canonicalPair t i ∈ globalLine .octahedral t := by
  intro t i
  rw [globalLine_eq_translated]
  apply (translatedLine_iff .octahedral _ _ _).mpr
  fin_cases i <;> exact Submodule.subset_span (by simp [canonicalPair])

abbrev rawPoint := RankThree.rawPoint
abbrev rawPair := RankThree.rawPair

def projected (f : Form) (t : Fin 122) (r : Fin 24) : Fin 2 → Scalar :=
  ![rawPair (rawPoint f (canonicalPair t 0)) (rawPoint f r),
    rawPair (rawPoint f (canonicalPair t 1)) (rawPoint f r)]

def cross (u v : Fin 2 → Scalar) : Scalar := u 0*v 1-u 1*v 0

/-- Componentwise pair-zero decision avoids any classical function-equality
instance in the executable projective filter. -/
instance (priority := 2000) scalarPairZero (v : Fin 2→Scalar) : Decidable (v=0) :=
  if h : v 0=0 ∧ v 1=0 then isTrue (by
    funext i
    fin_cases i
    · exact h.1
    · exact h.2)
  else isFalse (fun hz=>h ⟨congrFun hz 0,congrFun hz 1⟩)

/-- First literal index in each nonzero projected projective class.
This filter computes only from the old kernels and canonical root pair. -/
def projectedIndices (f : Form) (t : Fin 122) : Finset (Fin 24) :=
  Finset.univ.filter fun r => projected f t r ≠ 0 ∧
    ∀ s : Fin 24,s.val < r.val → projected f t s ≠ 0 →
      cross (projected f t r) (projected f t s) ≠ 0

def certificate (f : Form) (t : Fin 122) : Prop :=
  (projectedIndices f t).card = if (globalLine .octahedral t).card = 4 then 4 else 6


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
