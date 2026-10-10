import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGraph

/-! The symmetric-W escape also works with retained X. A nonzero vector
cannot be isotropic for both equality and disequality. Actual X vertices on
the three internal edges give the same nondegenerate GHZ core. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWX
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
namespace W
export GlobalCloseCompletionIndependentPinsWCore
  (w image image_eq gram core columns columns_determinant coordinate triangle_image core_ghz)
end W
namespace G
export GlobalCloseCompletionIndependentPinsWGraph (decorate graph order map_triangle)
end G
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action)
end T
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz eq3)
end C
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant determinant_ne_zero invertibleOfDeterminant)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def x : Signature K 2 := fun z=>Signature.disequality (z 0) (z 1)
def flip (f : Signature K 3) : Signature K 3 := fun z=>f ![z 0,!(z 1),z 2]
def gram (A : Kernel K) (i j : Bool) : K := A false i*A true j+A true i*A false j

theorem triangle_image (A : Kernel K) : T.triangle (flip (W.image A))=T.action (Matrix.of A)
    (W.core (gram A false false) (gram A false true) (gram A true true)) := by
  funext z
  simp [T.triangle,flip,W.image,T.action,W.core,gram,Fintype.sum_bool]
  ring

theorem determinant (A : Kernel K) : gram A false false*gram A true true-gram A false true^2=
    -(A false false*A true true-A false true*A true false)^2 := by
  simp only [gram]
  ring

theorem norm_nonzero [CharZero K] (A : Kernel K)
    (det : A false false*A true true-A false true*A true false≠0) :
    W.gram (1:K) A false false≠0 ∨ gram A false false≠0 := by
  by_cases he : W.gram (1:K) A false false≠0
  · exact Or.inl he
  · right
    intro hx
    have zeroE:=not_not.mp he
    have product : A false false*A true false=0 := by
      have two : (2:K)*(A false false*A true false)=0 := by simpa [gram,two_mul,mul_comm] using hx
      exact (mul_eq_zero.mp two).resolve_left (by norm_num)
    rcases mul_eq_zero.mp product with first|second
    · have other : A true false=0 := by
        have square : A true false^2=0 := by simpa [W.gram,first,pow_two] using zeroE
        exact sq_eq_zero_iff.mp square
      exact det (by rw [first,other];ring)
    · have other : A false false=0 := by
        have square : A false false^2=0 := by simpa [W.gram,second,pow_two] using zeroE
        exact sq_eq_zero_iff.mp square
      exact det (by rw [second,other];ring)

theorem core_basis (p q r : AlgebraicComplex) (hp : p≠0) (hd : p*r-q^2≠0) :
    ∃R : InvertibleKernel,W.core p q r=C.ghz R.matrix := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨d,square⟩:=IsAlgClosed.exists_pow_nat_eq (p*r-q^2) (by decide : 0<2)
  obtain ⟨c,cube⟩:=IsAlgClosed.exists_pow_nat_eq ((2:AlgebraicComplex)⁻¹) (by decide : 0<3)
  have dn : d≠0 := by intro zero;rw [zero,zero_pow (by decide : 2≠0)] at square;exact hd square.symm
  have cn : c≠0 := by
    intro zero
    rw [zero,zero_pow (by decide : 3≠0)] at cube
    exact (inv_ne_zero (by norm_num : (2:AlgebraicComplex)≠0)) cube.symm
  have det : B.determinant (W.columns p q d c)≠0 := by
    rw [B.determinant,W.columns_determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ cn)) hp) dn
  exact ⟨B.invertibleOfDeterminant (W.columns p q d c) det,W.core_ghz p q r d c square cube⟩

variable {s : ℕ} {a : ℕ→ℕ} {H : (i : Fin s)→Signature K (a i.val)}

theorem decorate_value (N : Macro H 3) (D : Macro H 2) (form : D.network.denote=x) :
    (G.decorate N D).network.denote=flip N.network.denote := by
  funext z
  rw [G.decorate,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,Tensor.reindex_apply,Signature.tensor_apply,form]
  have first (v : Bool) :
      (fun i : Fin 3=>(Fin.cons v (Fin.cons v z) : Fin 5→Bool) (G.order (Fin.castAdd 2 i)))=![z 0,v,z 2] := by
    funext i
    fin_cases i <;> rfl
  have second (v : Bool) :
      (fun i : Fin 2=>(Fin.cons v (Fin.cons v z) : Fin 5→Bool) (G.order (Fin.natAdd 3 i)))=![v,z 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [first,second]
  cases h : z 1 <;> simp [x,Signature.disequality,flip,h]

theorem map_flip (phi : K→+*AlgebraicComplex) (f : Signature K 3) :
    RingHomRealization.mapSignature phi (flip f)=flip (RingHomRealization.mapSignature phi f) := rfl

theorem produces (phi : K→+*AlgebraicComplex) (N : Macro H 3) (D : Macro H 2)
    (form : D.network.denote=x) (A : InvertibleKernel)
    (wForm : RingHomRealization.mapSignature phi N.network.denote=A.action W.w) :
    ∃v : Bool,∃R : InvertibleKernel,
      RingHomRealization.mapSignature phi (G.graph N D v).network.denote=C.ghz R.matrix := by
  rcases norm_nonzero A.matrix (B.determinant_ne_zero A) with ordinary|flipped
  · have det : W.gram (1:AlgebraicComplex) A.matrix false false*W.gram 1 A.matrix true true-
        W.gram 1 A.matrix false true^2≠0 := by
      rw [GlobalCloseCompletionIndependentPinsWCore.gram_determinant,one_mul]
      exact pow_ne_zero _ (B.determinant_ne_zero A)
    obtain ⟨R,hR⟩:=core_basis _ _ _ ordinary det
    refine ⟨false,A.comp R,?_⟩
    rw [G.graph,if_neg Bool.false_ne_true,GlobalCloseCompletionTernaryGHZGraph.value,G.map_triangle,wForm]
    change T.triangle (Signature.coordinateAction (fun _=>A.matrix) W.w)=_
    rw [←W.image_eq]
    have one : GlobalCloseCompletionIndependentPinsWCore.twist (1:AlgebraicComplex) (W.image A.matrix)=W.image A.matrix := by
      funext z
      simp [GlobalCloseCompletionIndependentPinsWCore.twist,GlobalCloseCompletionIndependentPinsWCore.sign]
    rw [←one,W.triangle_image,←W.coordinate,hR]
    exact Signature.coordinateAction_comp _ _ _
  · have det : gram A.matrix false false*gram A.matrix true true-gram A.matrix false true^2≠0 := by
      rw [determinant]
      exact neg_ne_zero.mpr (pow_ne_zero _ (B.determinant_ne_zero A))
    obtain ⟨R,hR⟩:=core_basis _ _ _ flipped det
    refine ⟨true,A.comp R,?_⟩
    rw [G.graph,if_pos rfl,GlobalCloseCompletionTernaryGHZGraph.value,decorate_value N D form,G.map_triangle,map_flip,wForm]
    change T.triangle (flip (Signature.coordinateAction (fun _=>A.matrix) W.w))=_
    rw [←W.image_eq,triangle_image,←W.coordinate,hR]
    exact Signature.coordinateAction_comp _ _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWX
end
