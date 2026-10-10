import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixSquare
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PairAffine

/-! Exact Affine witnesses for signed four-support residuals. The sign at
1100 is one actual even quadratic phase in the source class definition. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixAffine
open Holant Holant.Tractable Holant.Tractable.TwoTranslate Holant.Tractable.AffinePhase
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bd)
end O
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def phase : Signature AlgebraicComplex 4 := fun x=>if x 0 && x 1 then -1 else 1

def quadratic : QuadraticPhase 4 where
  constant := 0
  linear _ := 0
  mixed i j := if i=0 ∧ j=1 then 2 else 0
  even_mixed := by intro i j _; split_ifs <;> simp

theorem phase_affine : Affine phase := by
  have h := affine_quadratic_phase quadratic
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [phase,quadratic,QuadraticPhase.eval,Fin.sum_univ_succ,bitValue,fourthRootPhase,h0,h1,h2,h3,imaginaryUnit_sq]
  all_goals
    change (-1 : AlgebraicComplex)=imaginaryUnit^2
    exact imaginaryUnit_sq.symm

theorem signed_phase (b c d : AlgebraicComplex) : S.signed b c d=fun x=>T.normal 0 b c d x*phase x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.signed,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,phase,h0,h1,h2,h3]

theorem eo_affine (c d : AlgebraicComplex) (hc : c≠0) (fourth : c^4=d^4) : Affine (T.normal 0 0 c d) := by
  have h := EOBinaryPlaneTract.affine_lift (GlobalCloseCompletionC2PairAffine.binary_fourth c d hc fourth)
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,EOBinaryPlaneCore.lift,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]

theorem sparse_of_binary (b c : AlgebraicComplex) (binary : Affine (M.binary (P.symmetric c b))) : Affine (S.signed b c 0) := by
  have lift := EOBinaryPlaneTract.affine_lift binary
  have eo : Affine (T.normal 0 0 c b) := by
    convert lift using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,EOBinaryPlaneCore.lift,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]
  have h := eo.precompose (fun x i=>x (Equiv.swap (1 : Fin 4) 3 i)) (coordinates_isAffineMap (Equiv.swap (1 : Fin 4) 3))
  have unsigned : Affine (T.normal 0 b c 0) := by
    change Affine (Tensor.reindex (Equiv.swap (1 : Fin 4) 3) (T.normal 0 0 c b)) at h
    simpa only [O.swap_bd] using h
  rw [signed_phase]
  exact unsigned.mul phase_affine

theorem sparse_affine (b c : AlgebraicComplex) (hc : c≠0) (fourth : b^4=c^4) : Affine (S.signed b c 0) :=
  sparse_of_binary b c (GlobalCloseCompletionC2PairAffine.binary_fourth c b hc fourth.symm)

theorem sparse_zero_affine (b : AlgebraicComplex) : Affine (S.signed b 0 0) :=
  sparse_of_binary b 0 (GlobalCloseCompletionC2PairAffine.anti_affine b)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixAffine
end
