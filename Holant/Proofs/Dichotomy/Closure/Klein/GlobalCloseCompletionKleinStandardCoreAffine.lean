import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinChart

/-! The literal six-port Pauli core is Affine in its original ordered
coordinates. The witness is one even-parity support equation and one explicit
quadratic sign polynomial; no change of basis or backend classification is
used. This alone does not classify arbitrary higher stable Pauli tensors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardCoreAffine
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.EqualityQuaternary
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

/-- Exact ordered I/Z/X/J convention for the source's Bell labels. -/
def bell (d l : Bool) : Kernel AlgebraicComplex := fun a b=>
  if Bool.xor a b=d then (if l && a then -1 else 1) else 0

theorem bell_pauli (d l : Bool) :
    bell d l=Klein.E .standard (if d then (if l then 3 else 1) else if l then 2 else 0) := by
  funext a b
  cases d <;> cases l <;> cases a <;> cases b <;>
    norm_num [bell,Klein.E,Klein.basisQ,Klein.matrix,Klein.embed_apply,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

/-- The four literal summands defining H6 in the fixed three-pair ordering. -/
def core : Signature AlgebraicComplex 6 := fun x=>
  bell false false (x 0) (x 1)*bell false false (x 2) (x 3)*bell false false (x 4) (x 5)+
  bell false true (x 0) (x 1)*bell true true (x 2) (x 3)*bell true false (x 4) (x 5)+
  bell true false (x 0) (x 1)*bell false true (x 2) (x 3)*bell true true (x 4) (x 5)+
  bell true true (x 0) (x 1)*bell true false (x 2) (x 3)*bell false true (x 4) (x 5)

def support : AffineSystem 6 := ⟨1,fun _ _=>1,fun _=>0⟩

def phase : QuadraticPhase 6 where
  constant := 0
  linear := fun _=>0
  mixed j k := if (j=0 ∧ (k=2 ∨ k=3 ∨ k=4)) ∨ (j=1 ∧ k=4) ∨ (j=2 ∧ (k=4 ∨ k=5)) then 2 else 0
  even_mixed := by intro j k _; split_ifs <;> simp

theorem core_formula : core=affineFormula 1 support phase := by
  funext x
  dsimp only [affineFormula,AffineSystem.Holds,support,phase,QuadraticPhase.eval]
  simp only [Fin.sum_univ_succ,Fin.forall_fin_succ]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    norm_num [core,bell,affineFormula,support,AffineSystem.Holds,
      phase,QuadraticPhase.eval,Fin.sum_univ_succ,Fin.forall_fin_succ,
      bitValue,h0,h1,h2,h3,h4,h5,fourthRootPhase,imaginaryUnit_sq,ZMod.val_natCast] <;>
    norm_num [ZMod.val,imaginaryUnit_sq] <;> decide

theorem affine_core : Affine core := by
  rw [core_formula]
  exact affine_formula _ _ _


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardCoreAffine
end
