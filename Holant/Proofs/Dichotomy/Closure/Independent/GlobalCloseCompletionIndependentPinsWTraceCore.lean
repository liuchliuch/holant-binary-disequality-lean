import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWGeneralXCore
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZTrace

/-! The W triangle needs only a nonsingular symmetric trace-zero phase.
Among three cyclic orientations, equality or this phase has nonzero first
column contraction. All statements refer to the supplied physical phase. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWTraceCore
open Holant Holant.Tractable
namespace W
export GlobalCloseCompletionIndependentPinsWGeneralCore (image core gram triangle_image)
end W
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def gram (a b : K) (B C : Kernel K) (i j : Bool) : K :=
  a*(B false i*C false j-B true i*C true j)+b*(B false i*C true j+B true i*C false j)
def left (a b : K) (B : Kernel K) : Kernel K := fun i j=>
  if i then b*B false j-a*B true j else a*B false j+b*B true j
def twist (a b : K) (f : Signature K 3) : Signature K 3 := fun x=>
  f ![x 0,false,x 2]*(if x 1 then b else a)+
  f ![x 0,true,x 2]*(if x 1 then -a else b)

theorem twist_image (a b : K) (A B C : Kernel K) :
    twist a b (W.image A B C)=W.image A (left a b B) C := by
  funext x
  cases h : x 1 <;> simp [twist,W.image,left,h] <;> ring

theorem triangle_image (a b : K) (A B C : Kernel K) :
    T.triangle (twist a b (W.image A B C))=T.action (Matrix.of A)
      (W.core (gram a b B C false false) (gram a b B C false true)
        (gram a b B C true false) (gram a b B C true true)) := by
  rw [twist_image]
  have one : GlobalCloseCompletionIndependentPinsWCore.twist (1:K)
      (W.image A (left a b B) C)=W.image A (left a b B) C := by
    funext x
    simp [GlobalCloseCompletionIndependentPinsWCore.twist,GlobalCloseCompletionIndependentPinsWCore.sign]
  rw [←one,W.triangle_image]
  have entries (i j : Bool) : W.gram 1 (left a b B) C i j=gram a b B C i j := by
    simp [W.gram,left,gram]
    ring
  simp_rw [entries]

theorem gram_determinant (a b : K) (B C : Kernel K) :
    gram a b B C false false*gram a b B C true true-gram a b B C false true*gram a b B C true false=
      (-a^2-b*b)*(B false false*B true true-B false true*B true false)*
        (C false false*C true true-C false true*C true false) := by
  simp only [gram]
  ring

theorem choose_pair [CharZero K] (a b : K) (phase : -a^2-b*b≠0) (A B C : Kernel K)
    (ha : A false false*A true true-A false true*A true false≠0)
    (hb : B false false*B true true-B false true*B true false≠0)
    (hc : C false false*C true true-C false true*C true false≠0) :
    (∃v : Bool,(if v then gram a b B C false false else W.gram 1 B C false false)≠0) ∨
    (∃v : Bool,(if v then gram a b A B false false else W.gram 1 A B false false)≠0) ∨
    (∃v : Bool,(if v then gram a b C A false false else W.gram 1 C A false false)≠0) := by
  classical
  by_contra bad
  push_neg at bad
  obtain ⟨bc,ab,ca⟩:=bad
  have ebc:=bc false
  have eab:=ab false
  have eca:=ca false
  have tab:=ab true
  simp only [Bool.false_eq_true,ite_false,ite_true,W.gram,one_mul,gram] at ebc eab eca tab
  have u : A false false≠0 := by
    intro zero
    have v : A true false≠0 := by intro h;exact ha (by rw [zero,h];ring)
    have x : B true false=0 := (mul_eq_zero.mp (by simpa [zero] using eab)).resolve_left v
    have z : C true false=0 := (mul_eq_zero.mp (by simpa [zero] using eca)).resolve_right v
    have w : B false false≠0 := by intro h;exact hb (by rw [h,x];ring)
    have y : C false false≠0 := by intro h;exact hc (by rw [h,z];ring)
    exact (mul_ne_zero w y) (by simpa [x,z] using ebc)
  have v : A true false≠0 := by
    intro zero
    have w : B false false=0 := (mul_eq_zero.mp (by simpa [zero] using eab)).resolve_left u
    have y : C false false=0 := (mul_eq_zero.mp (by simpa [zero] using eca)).resolve_right u
    have x : B true false≠0 := by intro h;exact hb (by rw [w,h];ring)
    have z : C true false≠0 := by intro h;exact hc (by rw [y,h];ring)
    exact (mul_ne_zero x z) (by simpa [w,y] using ebc)
  have x : B true false≠0 := by
    intro zero
    have w : B false false=0 := (mul_eq_zero.mp (by simpa [zero] using eab)).resolve_left u
    exact hb (by rw [w,zero];ring)
  have z : C true false≠0 := by
    intro zero
    have y : C false false=0 := (mul_eq_zero.mp (by simpa [zero] using eca)).resolve_right u
    exact hc (by rw [y,zero];ring)
  have norm : A false false^2+A true false^2=0 := by
    have product : (A false false^2+A true false^2)*(B true false*C true false)=0 := by
      linear_combination A false false^2*ebc-A false false*C false false*eab+A true false*B true false*eca
    exact (mul_eq_zero.mp product).resolve_right (mul_ne_zero x z)
  have linear : a*A false false+b*A true false=0 := by
    have product : (-2*A true false*B true false)*(a*A false false+b*A true false)=0 := by
      linear_combination A false false*tab-(a*A false false+b*A true false)*eab-b*B true false*norm
    exact (mul_eq_zero.mp product).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) v) x)
  have coefficients : a^2+b^2=0 := by
    have product : (a^2+b^2)*A false false^2=0 := by
      linear_combination (a*A false false-b*A true false)*linear+b^2*norm
    exact (mul_eq_zero.mp product).resolve_right (pow_ne_zero _ u)
  apply phase
  linear_combination -coefficients


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWTraceCore
end
