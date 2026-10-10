import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZField
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZInverseFinite
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapSelection

/-! Derive both characteristic roots of the actual semisimple binary in
AlgebraicComplex, install exactly those two constants in a finite coefficient
field, and lift the same physical graph. Root equations are reflected through
the injective field map before invoking the proved inverse-chain source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRootInverseField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionSymmetricGHZField (field presentation table constant constant_value table_value lift lift_value controlled)
end E
namespace I
export GlobalCloseCompletionSymmetricGHZInverse (matrix)
export GlobalCloseCompletionSymmetricGHZInverseFinite (Extension produce)
end I
namespace C
export GlobalCloseCompletionSymmetricGHZCapSelection (discriminant Semisimple)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (N : NoXOrdinaryGraphAdjoin.Output H 2)

def ambient : Binary (K:=AlgebraicComplex):=(I.matrix H N).map (L.val.toRingHom : L→+*AlgebraicComplex)

theorem trace_value : Matrix.trace (ambient L H N)=((Matrix.trace (I.matrix H N) : L) : AlgebraicComplex) := by
  simp [ambient,Matrix.trace,Matrix.map_apply]

theorem det_value : Matrix.det (ambient L H N)=((Matrix.det (I.matrix H N) : L) : AlgebraicComplex) := by
  rw [det_entries,det_entries]
  simp [ambient,Matrix.map_apply]

structure Roots where
  first : AlgebraicComplex
  second : AlgebraicComplex
  distinct : first≠second
  first_nonzero : first≠0
  second_nonzero : second≠0
  trace : Matrix.trace (ambient L H N)=first+second
  determinant : Matrix.det (ambient L H N)=first*second

variable (det : Matrix.det (I.matrix H N)≠0) (discriminant : C.discriminant (I.matrix H N)≠0)
include det discriminant in
theorem roots_exist : Nonempty (Roots L H N) := by
  letI : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a,b,trace,determinant,_,_⟩:=Holant.Projective.BoundedTorsion.exists_eigenpair (ambient L H N)
  have live : a*b≠0 := by
    rw [←determinant,det_value]
    intro zero
    exact det (Subtype.ext zero)
  refine ⟨⟨a,b,?_,(mul_ne_zero_iff.mp live).1,(mul_ne_zero_iff.mp live).2,trace,determinant⟩⟩
  intro equal
  apply discriminant
  apply Subtype.ext
  have h : Matrix.trace (ambient L H N)^2-4*Matrix.det (ambient L H N)=0 := by
    rw [trace,determinant,equal]
    ring
  rw [trace_value,det_value] at h
  change (L.val.toRingHom : L→+*AlgebraicComplex) (C.discriminant (I.matrix H N))=0
  have coe (x : L) : L.val.toRingHom x=(x : AlgebraicComplex):=rfl
  simp only [C.discriminant,map_sub,map_pow,map_mul,map_ofNat]
  simpa only [coe] using h

def roots : Roots L H N:=Classical.choice (roots_exist L H N det discriminant)

variable (R : Roots L H N)
def extra : Fin 2→AlgebraicComplex:=![R.first,R.second]
abbrev field:=E.field L H (extra L H N R)
local instance : Algebra ℚ (field L H N R):=(field L H N R).algebra'
abbrev presentation:=E.presentation L H (extra L H N R)
abbrev table:=E.table L H (extra L H N R)
abbrev graph:=E.lift L H (extra L H N R) N
def first : field L H N R:=E.constant L H (extra L H N R) 0
def second : field L H N R:=E.constant L H (extra L H N R) 1

theorem first_value : (first L H N R : AlgebraicComplex)=R.first := rfl
theorem second_value : (second L H N R : AlgebraicComplex)=R.second := rfl

theorem matrix_value : (I.matrix (table L H N R) (graph L H N R)).map ((field L H N R).val.toRingHom : field L H N R→+*AlgebraicComplex)=ambient L H N := by
  funext i j
  exact congrFun (E.lift_value L H (extra L H N R) N) ![i,j]

theorem distinct : first L H N R≠second L H N R := by
  intro equal
  exact R.distinct (congrArg (fun z : field L H N R=>(z : AlgebraicComplex)) equal)

theorem first_nonzero : first L H N R≠0 := by
  intro zero
  exact R.first_nonzero (congrArg (fun z : field L H N R=>(z : AlgebraicComplex)) zero)

theorem second_nonzero : second L H N R≠0 := by
  intro zero
  exact R.second_nonzero (congrArg (fun z : field L H N R=>(z : AlgebraicComplex)) zero)

theorem trace : Matrix.trace (I.matrix (table L H N R) (graph L H N R))=first L H N R+second L H N R := by
  apply Subtype.ext
  change ((field L H N R).val.toRingHom : field L H N R→+*AlgebraicComplex) (Matrix.trace (I.matrix (table L H N R) (graph L H N R)))=R.first+R.second
  rw [AddMonoidHom.map_trace,matrix_value]
  exact R.trace

theorem determinant : Matrix.det (I.matrix (table L H N R) (graph L H N R))=first L H N R*second L H N R := by
  apply Subtype.ext
  change ((field L H N R).val.toRingHom : field L H N R→+*AlgebraicComplex) (Matrix.det (I.matrix (table L H N R) (graph L H N R)))=R.first*R.second
  rw [RingHom.map_det]
  change Matrix.det ((I.matrix (table L H N R) (graph L H N R)).map
    ((field L H N R).val.toRingHom : field L H N R→+*AlgebraicComplex))=R.first*R.second
  rw [matrix_value]
  exact R.determinant

def extension : I.Extension (table L H N R) (presentation L H N R) (graph L H N R) :=
  I.produce (table L H N R) (presentation L H N R) (graph L H N R)
    (first L H N R) (second L H N R) (distinct L H N R)
    (first_nonzero L H N R) (second_nonzero L H N R) (trace L H N R) (determinant L H N R)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRootInverseField
end
