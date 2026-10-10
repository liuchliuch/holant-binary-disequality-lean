import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSymmetricMoments
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZSymmetry
import Holant.Tractable.Anchor

/-! Every actual symmetric prime ternary is in the GHZ or W orbit, with a
single genuine invertible algebraic matrix. Vanishing Hankel minors give an
explicit forbidden unary/binary split; no tensor-orbit classifier is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricDecomposition
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
namespace M
export GlobalCloseCompletionIndependentPinsSymmetricMoments (table h0 h1 h2 first_minor)
end M
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
end C
namespace W
export GlobalCloseCompletionIndependentPinsWCore (w)
end W
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant diagonal)
end B
namespace S
export GlobalCloseCompletionTernaryGHZSymmetry (symmetric values)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

private def splitPorts : (Fin 1⊕Fin 2)≃Fin 3 := finSumFinEquiv

private theorem left_ports (x : Fin 3→Bool) :
    (fun i : Fin 1=>x (splitPorts (.inl i)))=(fun _=>x 0) := by
  funext i
  fin_cases i
  rfl
private theorem right_ports (x : Fin 3→Bool) :
    (fun i : Fin 2=>x (splitPorts (.inr i)))=![x 1,x 2] := by
  funext i
  fin_cases i <;> rfl

theorem minor_nonzero (p q r s : K) (prime : Prime (⟨3,M.table p q r s⟩ : AnySignature K)) :
    M.h0 p q r≠0 ∨ M.h1 p q r s≠0 ∨ M.h2 q r s≠0 := by
  classical
  by_contra bad
  push_neg at bad
  obtain ⟨h0,h1,h2⟩:=bad
  apply prime.2
  by_cases hp : p=0
  · have hq : q=0 := by
      have hz : q^2=0 := by simpa [M.h0,hp] using h0
      exact sq_eq_zero_iff.mp hz
    have hr : r=0 := by
      have hz : r^2=0 := by simpa [M.h2,hq] using h2
      exact sq_eq_zero_iff.mp hz
    let l : Signature K 1:=fun x=>if x 0 then 1 else 0
    let t : Signature K 2:=fun x=>if x 0 && x 1 then s else 0
    refine ⟨⟨1,l⟩,⟨2,t⟩,⟨{
      left_pos:=by change 0<1;omega
      right_pos:=by change 0<2;omega
      ports:=splitPorts
      scale:=1
      equation:=?_ }⟩⟩
    funext x
    change M.table p q r s x=(1:K)*(l (fun i=>x (splitPorts (.inl i)))*t (fun i=>x (splitPorts (.inr i))))
    rw [left_ports,right_ports]
    cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
      simp [M.table,l,t,e0,e1,e2,hp,hq,hr]
  · let l : Signature K 1:=fun x=>if x 0 then q/p else 1
    let t : Signature K 2:=fun x=>if x 0 then (if x 1 then r else q) else (if x 1 then q else p)
    refine ⟨⟨1,l⟩,⟨2,t⟩,⟨{
      left_pos:=by change 0<1;omega
      right_pos:=by change 0<2;omega
      ports:=splitPorts
      scale:=1
      equation:=?_ }⟩⟩
    funext x
    change M.table p q r s x=(1:K)*(l (fun i=>x (splitPorts (.inl i)))*t (fun i=>x (splitPorts (.inr i))))
    rw [left_ports,right_ports]
    cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
      simp [M.table,l,t,e0,e1,e2,hp]
    all_goals simp only [M.h0,M.h1] at h0 h1
    all_goals field_simp [hp]
    all_goals first
      | linear_combination h0
      | linear_combination h1

theorem reverse (p q r s : AlgebraicComplex) :
    bitFlipBasis.action (M.table p q r s)=M.table s r q p := by
  funext x
  rw [bitFlipBasis_action]
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [M.table,e0,e1,e2]

theorem diagonal_decomposition (p s : AlgebraicComplex) (hp : p≠0) (hs : s≠0) :
    ∃R : InvertibleKernel,M.table p 0 0 s=C.ghz R.matrix := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨c,hc⟩:=IsAlgClosed.exists_pow_nat_eq p (by decide : 0<3)
  obtain ⟨d,hd⟩:=IsAlgClosed.exists_pow_nat_eq s (by decide : 0<3)
  have cn : c≠0 := by intro zero;rw [zero,zero_pow (by decide : 3≠0)] at hc;exact hp hc.symm
  have dn : d≠0 := by intro zero;rw [zero,zero_pow (by decide : 3≠0)] at hd;exact hs hd.symm
  have determinant : B.determinant (B.diagonal c d)≠0 := by
    simpa [B.determinant,B.diagonal] using mul_ne_zero cn dn
  refine ⟨B.invertibleOfDeterminant (B.diagonal c d) determinant,?_⟩
  funext x
  rw [C.ghz_value]
  change M.table p 0 0 s x=B.diagonal c d (x 0) false*B.diagonal c d (x 1) false*B.diagonal c d (x 2) false+
    B.diagonal c d (x 0) true*B.diagonal c d (x 1) true*B.diagonal c d (x 2) true
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [M.table,B.diagonal,e0,e1,e2]
  · simpa only [pow_succ,pow_zero,one_mul] using hc.symm
  · simpa only [pow_succ,pow_zero,one_mul] using hd.symm

theorem classified (p q r s : AlgebraicComplex)
    (prime : Prime (⟨3,M.table p q r s⟩ : AnySignature AlgebraicComplex)) :
    (∃R : InvertibleKernel,M.table p q r s=C.ghz R.matrix) ∨
    (∃R : InvertibleKernel,M.table p q r s=R.action W.w) := by
  by_cases h0 : M.h0 p q r≠0
  · exact M.first_minor p q r s h0
  have zero0 := not_not.mp h0
  by_cases h2 : M.h2 q r s≠0
  · have hr : M.h0 s r q≠0 := by simpa only [M.h0,M.h2,mul_comm] using h2
    rcases M.first_minor s r q p hr with ⟨R,hR⟩|⟨R,hR⟩
    · left
      refine ⟨bitFlipBasis.comp R,?_⟩
      calc
        M.table p q r s=bitFlipBasis.action (M.table s r q p) := (reverse s r q p).symm
        _=bitFlipBasis.action (C.ghz R.matrix) := by rw [hR]
        _=C.ghz (bitFlipBasis.comp R).matrix := (InvertibleKernel.comp_action bitFlipBasis R _).symm
    · right
      refine ⟨bitFlipBasis.comp R,?_⟩
      calc
        M.table p q r s=bitFlipBasis.action (M.table s r q p) := (reverse s r q p).symm
        _=bitFlipBasis.action (R.action W.w) := by rw [hR]
        _=(bitFlipBasis.comp R).action W.w := (InvertibleKernel.comp_action bitFlipBasis R _).symm
  have zero2:=not_not.mp h2
  have hn : M.h1 p q r s≠0 := by
    rcases minor_nonzero p q r s prime with first|second|third
    · exact (first zero0).elim
    · exact second
    · exact (third zero2).elim
  have hq : q=0 := by
    have eqn : q*M.h1 p q r s=0 := by
      simp only [M.h0,M.h1,M.h2] at zero0 zero2 ⊢
      linear_combination p*zero2+r*zero0
    exact (mul_eq_zero.mp eqn).resolve_right hn
  have hr : r=0 := by
    have hz : r^2=0 := by simpa [M.h2,hq] using zero2
    exact sq_eq_zero_iff.mp hz
  have hps : p*s≠0 := by simpa [M.h1,hq,hr] using hn
  rw [hq,hr]
  exact Or.inl (diagonal_decomposition p s (mul_ne_zero_iff.mp hps).1 (mul_ne_zero_iff.mp hps).2)

theorem symmetric_prime (f : Signature AlgebraicComplex 3)
    (symmetric : f=S.symmetric (S.values f)) (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) :
    (∃R : InvertibleKernel,f=C.ghz R.matrix) ∨ (∃R : InvertibleKernel,f=R.action W.w) := by
  have table : f=M.table (f ![false,false,false]) (f ![true,false,false])
      (f ![true,true,false]) (f ![true,true,true]) := symmetric
  rw [table] at prime ⊢
  exact classified _ _ _ _ prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsSymmetricDecomposition
end
