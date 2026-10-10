import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryAction

/-! Classification after one ternary slice is normalized to E00. A live
opposite corner gives an explicit GHZ decomposition. A zero opposite corner
forces both crossed entries to survive by primality, giving explicit W. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryNormal
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
namespace T
export GlobalCloseCompletionIndependentPinsTernaryAction (Orbit action ghz w)
end T
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end B
namespace G
export GlobalCloseCompletionTernaryGHZCore (ghz)
end G
namespace W
export GlobalCloseCompletionIndependentPinsWGeneralCore (image)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

def matrix (a b c d : AlgebraicComplex) : Kernel AlgebraicComplex
  | false,false=>a
  | false,true=>b
  | true,false=>c
  | true,true=>d

def normal (a b c d : AlgebraicComplex) : Signature AlgebraicComplex 3 := fun x=>
  if x 0 then (if x 1 then 0 else if x 2 then 0 else 1) else matrix a b c d (x 1) (x 2)

private def firstPorts : (Fin 2⊕Fin 1)≃Fin 3:=finSumFinEquiv
private def middleOrder : Equiv.Perm (Fin 3) where
  toFun:=![1,0,2]
  invFun:=![1,0,2]
  left_inv:=by decide
  right_inv:=by decide
private def middlePorts : (Fin 1⊕Fin 2)≃Fin 3:=finSumFinEquiv.trans middleOrder

theorem crossed_nonzero (a b c : AlgebraicComplex)
    (prime : Prime (⟨3,normal a b c 0⟩ : AnySignature AlgebraicComplex)) : b≠0 ∧ c≠0 := by
  constructor
  · intro hb
    let l : Signature AlgebraicComplex 2:=fun x=>if x 0 then (if x 1 then 0 else 1) else (if x 1 then c else a)
    let r : Signature AlgebraicComplex 1:=fun x=>if x 0 then 0 else 1
    apply prime.2
    refine ⟨⟨2,l⟩,⟨1,r⟩,⟨{
      left_pos:=by change 0<2;omega
      right_pos:=by change 0<1;omega
      ports:=firstPorts
      scale:=1
      equation:=?_ }⟩⟩
    funext x
    have left : (fun i : Fin 2=>x (firstPorts (.inl i)))=![x 0,x 1] := by funext i;fin_cases i <;> rfl
    have right : (fun i : Fin 1=>x (firstPorts (.inr i)))=(fun _=>x 2) := by funext i;fin_cases i;rfl
    change normal a b c 0 x=(1:AlgebraicComplex)*
      (l (fun i=>x (firstPorts (.inl i)))*r (fun i=>x (firstPorts (.inr i))))
    rw [left,right]
    cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
      simp [normal,matrix,l,r,e0,e1,e2,hb]
  · intro hc
    let l : Signature AlgebraicComplex 1:=fun x=>if x 0 then 0 else 1
    let r : Signature AlgebraicComplex 2:=fun x=>if x 0 then (if x 1 then 0 else 1) else (if x 1 then b else a)
    apply prime.2
    refine ⟨⟨1,l⟩,⟨2,r⟩,⟨{
      left_pos:=by change 0<1;omega
      right_pos:=by change 0<2;omega
      ports:=middlePorts
      scale:=1
      equation:=?_ }⟩⟩
    funext x
    have left : (fun i : Fin 1=>x (middlePorts (.inl i)))=(fun _=>x 1) := by
      funext i;fin_cases i;rfl
    have right : (fun i : Fin 2=>x (middlePorts (.inr i)))=![x 0,x 2] := by
      funext i;fin_cases i <;> rfl
    change normal a b c 0 x=(1:AlgebraicComplex)*
      (l (fun i=>x (middlePorts (.inl i)))*r (fun i=>x (middlePorts (.inr i))))
    rw [left,right]
    cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
      simp [normal,matrix,l,r,e0,e1,e2,hc]

theorem ghz_normal (a b c d : AlgebraicComplex) (hd : d≠0) : T.Orbit (normal a b c d) := by
  let A:=B.invertibleOfDeterminant (matrix (a-b*c/d) d 1 0)
    (by simpa [B.determinant,matrix] using neg_ne_zero.mpr hd)
  let B':=B.invertibleOfDeterminant (matrix 1 (b/d) 0 1) (by norm_num [B.determinant,matrix])
  let C:=B.invertibleOfDeterminant (matrix 1 (c/d) 0 1) (by norm_num [B.determinant,matrix])
  left
  refine ⟨A,B',C,?_⟩
  rw [T.ghz]
  funext x
  simp only [G.ghz,Fintype.sum_bool]
  change normal a b c d x=matrix (a-b*c/d) d 1 0 (x 0) true*matrix 1 (b/d) 0 1 (x 1) true*matrix 1 (c/d) 0 1 (x 2) true+
    matrix (a-b*c/d) d 1 0 (x 0) false*matrix 1 (b/d) 0 1 (x 1) false*matrix 1 (c/d) 0 1 (x 2) false
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [normal,matrix,e0,e1,e2,hd]
  all_goals field_simp [hd]
  all_goals ring

theorem w_normal (a b c : AlgebraicComplex) (hb : b≠0) (hc : c≠0) : T.Orbit (normal a b c 0) := by
  let A:=B.invertibleOfDeterminant (matrix 1 a 0 1) (by norm_num [B.determinant,matrix])
  let B':=B.invertibleOfDeterminant (matrix 1 0 0 c) (by simpa [B.determinant,matrix] using hc)
  let C:=B.invertibleOfDeterminant (matrix 1 0 0 b) (by simpa [B.determinant,matrix] using hb)
  right
  refine ⟨A,B',C,?_⟩
  rw [T.w]
  funext x
  change normal a b c 0 x=W.image (matrix 1 a 0 1) (matrix 1 0 0 c) (matrix 1 0 0 b) x
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [normal,matrix,W.image,e0,e1,e2]

theorem classified (a b c d : AlgebraicComplex)
    (prime : Prime (⟨3,normal a b c d⟩ : AnySignature AlgebraicComplex)) : T.Orbit (normal a b c d) := by
  by_cases hd : d=0
  · subst d
    have h:=crossed_nonzero a b c prime
    exact w_normal a b c h.1 h.2
  · exact ghz_normal a b c d hd

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryNormal
end
