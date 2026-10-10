import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWCore

/-! Exact four-moment decomposition of a symmetric ternary. Distinct roots
give two nonzero cubes; a repeated root gives the W orbit. The recurrence and
all denominators are proved from the literal coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricMoments
open Holant Holant.Tractable
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
end C
namespace W
export GlobalCloseCompletionIndependentPinsWCore (w image image_eq)
end W
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K]

def table (p q r s : K) : Signature K 3 := fun x=>
  if x 0 then (if x 1 then (if x 2 then s else r) else (if x 2 then r else q))
  else if x 1 then (if x 2 then r else q) else (if x 2 then q else p)

def h0 (p q r : K) : K:=p*r-q^2
def h1 (p q r s : K) : K:=p*s-q*r
def h2 (q r s : K) : K:=q*s-r^2

theorem recurrence (p q r s : K) (hn : h0 p q r≠0) :
    r=(h1 p q r s/h0 p q r)*q-(h2 q r s/h0 p q r)*p ∧
    s=(h1 p q r s/h0 p q r)*r-(h2 q r s/h0 p q r)*q := by
  constructor <;> field_simp [hn] <;> simp only [h0,h1,h2] <;> ring

def left (p q u v : K) : K := (q-p*v)/(u-v)
def right (p q u v : K) : K := (p*u-q)/(u-v)

theorem moments (p q r s u v : K) (distinct : u-v≠0)
    (hr : r=(u+v)*q-u*v*p) (hs : s=(u+v)*r-u*v*q) :
    p=left p q u v+right p q u v ∧
    q=left p q u v*u+right p q u v*v ∧
    r=left p q u v*u^2+right p q u v*v^2 ∧
    s=left p q u v*u^3+right p q u v*v^3 := by
  have first : p=left p q u v+right p q u v := by
    unfold left right
    field_simp [distinct]
    ring
  have second : q=left p q u v*u+right p q u v*v := by
    unfold left right
    field_simp [distinct]
    ring
  have third : r=left p q u v*u^2+right p q u v*v^2 := by
    linear_combination hr+(u+v)*second-u*v*first
  refine ⟨first,second,third,?_⟩
  linear_combination hs+(u+v)*third-u*v*second

theorem weights_nonzero (p q r s u v : K) (distinct : u-v≠0)
    (hr : r=(u+v)*q-u*v*p) (hs : s=(u+v)*r-u*v*q) (hn : h0 p q r≠0) :
    left p q u v≠0 ∧ right p q u v≠0 := by
  obtain ⟨hp,hq,hr',_⟩:=moments p q r s u v distinct hr hs
  have determinant : h0 p q r=left p q u v*right p q u v*(u-v)^2 := by
    unfold h0
    linear_combination r*hp+(left p q u v+right p q u v)*hr'-(q+left p q u v*u+right p q u v*v)*hq
  have live : left p q u v*right p q u v≠0 := by
    intro zero
    exact hn (by rw [determinant,zero,zero_mul])
  exact mul_ne_zero_iff.mp live

section Algebraic
variable (p q r s : AlgebraicComplex)

def momentMatrix (c d u v : AlgebraicComplex) : Kernel AlgebraicComplex
  | false,false=>c
  | false,true=>d
  | true,false=>c*u
  | true,true=>d*v

theorem distinct_decomposition (u v : AlgebraicComplex) (distinct : u-v≠0)
    (hr : r=(u+v)*q-u*v*p) (hs : s=(u+v)*r-u*v*q) (hn : h0 p q r≠0) :
    ∃R : InvertibleKernel,table p q r s=C.ghz R.matrix := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  have live:=weights_nonzero p q r s u v distinct hr hs hn
  obtain ⟨c,hc⟩:=IsAlgClosed.exists_pow_nat_eq (left p q u v) (by decide : 0<3)
  obtain ⟨d,hd⟩:=IsAlgClosed.exists_pow_nat_eq (right p q u v) (by decide : 0<3)
  have cn : c≠0 := by intro zero;rw [zero,zero_pow (by decide : 3≠0)] at hc;exact live.1 hc.symm
  have dn : d≠0 := by intro zero;rw [zero,zero_pow (by decide : 3≠0)] at hd;exact live.2 hd.symm
  have determinant : B.determinant (momentMatrix c d u v)≠0 := by
    have he : B.determinant (momentMatrix c d u v)= -c*d*(u-v) := by
      simp only [B.determinant,momentMatrix]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr cn) dn) distinct
  refine ⟨B.invertibleOfDeterminant (momentMatrix c d u v) determinant,?_⟩
  obtain ⟨hp,hq,hr',hs'⟩:=moments p q r s u v distinct hr hs
  funext x
  rw [C.ghz_value]
  change table p q r s x=momentMatrix c d u v (x 0) false*momentMatrix c d u v (x 1) false*
    momentMatrix c d u v (x 2) false+momentMatrix c d u v (x 0) true*momentMatrix c d u v (x 1) true*
    momentMatrix c d u v (x 2) true
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp only [table,momentMatrix,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true]
  all_goals ring_nf
  all_goals rw [hc,hd]
  all_goals first | exact hp | exact hq | exact hr' | exact hs' | simpa [mul_comm] using hq | simpa [mul_comm] using hr' | simpa [mul_comm] using hs'

def repeatedMatrix (p q u : AlgebraicComplex) : Kernel AlgebraicComplex
  | false,false=>1
  | false,true=>p/3
  | true,false=>u
  | true,true=>q-2*p*u/3

theorem repeated_decomposition (u : AlgebraicComplex)
    (hr : r=2*u*q-u^2*p) (hs : s=3*u^2*q-2*u^3*p) (hn : h0 p q r≠0) :
    ∃R : InvertibleKernel,table p q r s=R.action W.w := by
  have dn : q-p*u≠0 := by
    intro zero
    apply hn
    rw [h0,hr]
    have hq : q=p*u := sub_eq_zero.mp zero
    rw [hq]
    ring
  have determinant : B.determinant (repeatedMatrix p q u)≠0 := by
    have he : B.determinant (repeatedMatrix p q u)=q-p*u := by
      simp only [B.determinant,repeatedMatrix]
      ring
    rw [he]
    exact dn
  refine ⟨B.invertibleOfDeterminant (repeatedMatrix p q u) determinant,?_⟩
  change table p q r s=Signature.coordinateAction (fun _=>repeatedMatrix p q u) W.w
  rw [←W.image_eq]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp only [table,W.image,repeatedMatrix,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true,hr,hs]
  all_goals ring

/-- The literal nonsingular first Hankel minor supplies the complete
GHZ/W distinction, including all vanishing leading-coefficient cases. -/
theorem first_minor (hn : h0 p q r≠0) :
    (∃R : InvertibleKernel,table p q r s=C.ghz R.matrix) ∨
    (∃R : InvertibleKernel,table p q r s=R.action W.w) := by
  let S:=h1 p q r s/h0 p q r
  let P:=h2 q r s/h0 p q r
  have recurrent:=recurrence p q r s hn
  change r=S*q-P*p ∧ s=S*r-P*q at recurrent
  by_cases double : S^2-4*P=0
  · right
    apply repeated_decomposition p q r s (S/2) _ _ hn
    · rw [recurrent.1]
      linear_combination p*double/4
    · rw [recurrent.2,recurrent.1]
      linear_combination (S*p+q)*double/4
  · left
    letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
    obtain ⟨d,hd⟩:=IsAlgClosed.exists_pow_nat_eq (S^2-4*P) (by decide : 0<2)
    have dn : d≠0 := by intro zero;rw [zero,zero_pow (by decide : 2≠0)] at hd;exact double hd.symm
    let u:=(S+d)/2
    let v:=(S-d)/2
    have sum : u+v=S := by dsimp [u,v];ring
    have product : u*v=P := by dsimp [u,v];linear_combination -hd/4
    have distinct : u-v≠0 := by convert dn using 1;dsimp [u,v];ring
    apply distinct_decomposition p q r s u v distinct _ _ hn
    · rw [sum,product]
      exact recurrent.1
    · rw [sum,product]
      exact recurrent.2

end Algebraic
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricMoments
end
