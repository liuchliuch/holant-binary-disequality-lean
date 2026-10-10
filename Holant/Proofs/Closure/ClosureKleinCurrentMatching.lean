import Holant.Proofs.Closure.ClosureKleinCurrentRows

/-! Exact all-arity canonical standard/exotic matching products derived from
the actual CURRENT source matching witnesses. Original ordered ports, the
original global scalar and all original factor coefficients remain explicit.
No six/eight-port classification is assumed or concluded by this mapping. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open scoped BigOperators
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

def CanonicalMatching {n : ℕ} (row : K.Kind) (q : Signature AlgebraicComplex n) : Prop :=
  q=0 ∨ ∃ M : Presentation AlgebraicComplex (Fin n),∃ labels : Fin M.edges → Fin 4,
    M.scalar≠0 ∧ (∀ e,M.matrix e=K.E row (labels e)) ∧ q=M.tensor

structure MatchingReceipt {n : ℕ} (f : Signature (OI.K G) n) where
  original : Presentation (OI.K G) (Fin n)
  valid : original.Valid (actualTransfers P.family)
  nonzero : original.scalar≠0
  sourceEquation : f=original.tensor
  labels : Fin original.edges → Fin 4
  coefficient : Fin original.edges → OI.K G
  coefficient_nonzero : ∀ e,coefficient e≠0
  factorEquation : ∀ e,(original.matrix e).map (ClosureSourceRows.embedding G)=
    scale (ClosureSourceRows.embedding G (coefficient e))
      (K.E (kind G P torsion cardinal noncyclic) (labels e))

namespace MatchingReceipt
variable {n : ℕ} {f : Signature (OI.K G) n}
variable (R : MatchingReceipt G P torsion cardinal noncyclic f)

def combined : OI.K G := R.original.scalar*∏ e,R.coefficient e
theorem combined_nonzero : R.combined≠0 :=
  mul_ne_zero R.nonzero (Finset.prod_ne_zero_iff.mpr (fun e _ => R.coefficient_nonzero e))

def canonical : Presentation AlgebraicComplex (Fin n) where
  edges := R.original.edges
  ports := R.original.ports
  matrix := fun e => Matrix.of (K.E (kind G P torsion cardinal noncyclic) (R.labels e))
  scalar := ClosureSourceRows.embedding G R.combined

@[simp] theorem canonical_ports : R.canonical.ports=R.original.ports := rfl
@[simp] theorem canonical_edges : R.canonical.edges=R.original.edges := rfl
@[simp] theorem canonical_scalar : R.canonical.scalar=ClosureSourceRows.embedding G R.combined := rfl

theorem mappedEquation : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f=R.canonical.tensor := by
  funext x
  change ClosureSourceRows.embedding G (f x)=_
  rw [congrFun R.sourceEquation x]
  simp only [Presentation.tensor,productValue,map_mul,map_prod,canonical,combined]
  have factor (e : Fin R.original.edges) :
      ClosureSourceRows.embedding G
        (R.original.matrix e (x (R.original.ports (e,false))) (x (R.original.ports (e,true))))=
      ClosureSourceRows.embedding G (R.coefficient e)*
        K.E (kind G P torsion cardinal noncyclic) (R.labels e)
          (x (R.original.ports (e,false))) (x (R.original.ports (e,true))) :=
    congrFun (congrFun (R.factorEquation e) _) _
  simp only [factor,Finset.prod_mul_distrib,map_mul,map_prod,Matrix.of_apply,mul_assoc]

include R in
theorem canonical_matching : CanonicalMatching (kind G P torsion cardinal noncyclic)
    (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := by
  right
  exact ⟨R.canonical,R.labels,(map_ne_zero _).mpr R.combined_nonzero,fun _ => rfl,R.mappedEquation⟩
end MatchingReceipt

inductive MatchingResult {n : ℕ} (f : Signature (OI.K G) n) : Type where
  | zero (equation : f=0)
  | product (receipt : MatchingReceipt G P torsion cardinal noncyclic f)

theorem matchingResult_exists {n : ℕ} (f : Signature (OI.K G) n)
    (actual : MatchingOrZero (actualTransfers P.family) f) :
    Nonempty (MatchingResult G P torsion cardinal noncyclic f) := by
  rcases actual with zero | ⟨M,valid,nonzero,equation⟩
  · exact ⟨.zero zero⟩
  · have rows := fun e => safe_factor_row G P torsion cardinal noncyclic (M.matrix e) (valid e)
    choose labels coefficient coefficients factorEquation using rows
    exact ⟨.product ⟨M,valid,nonzero,equation,labels,coefficient,coefficients,factorEquation⟩⟩

def matchingResult {n : ℕ} (f : Signature (OI.K G) n)
    (actual : MatchingOrZero (actualTransfers P.family) f) :
    MatchingResult G P torsion cardinal noncyclic f :=
  Classical.choice (matchingResult_exists G P torsion cardinal noncyclic f actual)

theorem matching_mapped {n : ℕ} (f : Signature (OI.K G) n)
    (actual : MatchingOrZero (actualTransfers P.family) f) :
    CanonicalMatching (kind G P torsion cardinal noncyclic)
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := by
  cases matchingResult G P torsion cardinal noncyclic f actual with
  | zero equation =>
    left
    funext x
    change ClosureSourceRows.embedding G (f x)=0
    rw [equation]
    exact map_zero _
  | product receipt => exact receipt.canonical_matching

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
