import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBitFlip
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryLoop

/-! Exact small-factor column uniqueness at an arbitrary complementary
support pivot. The outside-coordinate flip is semantic proof data only;
all conclusions concern the original tensor and its original port order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinColumn
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionUnaryBitFlip (word value word_zero word_twice tensorClosure)
end F
namespace B
export GlobalCloseCompletionUnaryBinaryFactor (pair outside small_factor_identity)
end B
namespace L
export GlobalCloseCompletionUnaryBinaryLoop (join pair_word pair_bottom outside_join section_minor)
end L
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {m : ℕ}

 theorem outside_flip (x : Fin 2→Bool) (y y0 : Fin m→Bool) :
    F.word (L.join (fun _=>false) y0) (L.join x y)=L.join x (F.word y0 y) := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;> simp [F.word,L.join]

 theorem pair_join (x : Fin 2→Bool) :
    B.pair (0 : Fin (m+2)) 1 (x 0) (x 1)=L.join x (fun _=>false) := by
  rw [L.pair_word]
  rfl

 theorem origin_join : L.join (fun _ : Fin 2=>false) (fun _ : Fin m=>false)=(fun _=>false) := by
  funext i
  refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i

 theorem factor_identity (f : Signature K (m+2)) (g : Signature K 2)
    (y0 : Fin m→Bool) (c : K) (nonzero : c≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (column : ∀x,f (L.join x y0)=c*g x)
    (small : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) f)
    (x : Fin 2→Bool) (y : Fin m→Bool) :
    f (L.join x y)*g (fun _=>false)=g x*f (L.join (fun _=>false) y) := by
  let mask := L.join (fun _ : Fin 2=>false) y0
  let shifted := F.value mask f
  have shift (a : Fin 2→Bool) (b : Fin m→Bool) :
      shifted (L.join a b)=f (L.join a (F.word y0 b)) := by
    change f (F.word mask (L.join a b))=_
    rw [outside_flip]
  have sections (a b : Bool) : shifted (B.pair 0 1 a b)=g ![a,b]*c := by
    rw [L.pair_word]
    change shifted (L.join ![a,b] (fun _=>false))=_
    rw [shift,F.word_zero,column,mul_comm]
  have minor : I.minor shifted 0 1≠0 := by
    rw [L.section_minor shifted g c sections]
    exact mul_ne_zero det (pow_ne_zero 2 nonzero)
  have zero : shifted (fun _=>false)=c*g (fun _=>false) := by
    rw [←origin_join,shift,F.word_zero,column]
  have identity := B.small_factor_identity shifted (F.tensorClosure mask f small)
    (0 : Fin (m+2)) 1 Fin.zero_ne_one minor (L.join x (F.word y0 y))
  rw [zero,L.outside_join] at identity
  change shifted (L.join x (F.word y0 y))*(c*g (fun _=>false))=
    shifted (B.pair 0 1 (x 0) (x 1))*shifted (L.join (fun _=>false) (F.word y0 y)) at identity
  rw [pair_join,shift,shift,shift,F.word_zero,F.word_twice,column] at identity
  apply mul_left_cancel₀ nonzero
  linear_combination identity

/-- The exact original-column factor is selected internally from the old
00 section. No extra factorisation witness or physical bit-flip is supplied. -/
theorem factor (f : Signature K (m+2)) (g : Signature K 2)
    (y0 : Fin m→Bool) (c : K) (nonzero : c≠0) (g0 : g (fun _=>false)≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (column : ∀x,f (L.join x y0)=c*g x)
    (small : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) f) :
    ∃h : Signature K m,∀x y,f (L.join x y)=g x*h y := by
  refine ⟨fun y=>f (L.join (fun _=>false) y)/g (fun _=>false),?_⟩
  intro x y
  rw [←mul_div_assoc]
  exact (eq_div_iff g0).mpr (factor_identity f g y0 c nonzero det column small x y)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinColumn
end
