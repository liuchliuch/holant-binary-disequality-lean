import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4SparseFactors

/-! Original-field primality excludes exactly the determinant-zero sparse
anchor cases. Reindexing transports the same factor partition and scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4PrimeTools
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
namespace F
export GlobalCloseCompletionC2Q4SparseFactors (signed_not_prime pair_not_prime eo_not_prime)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

theorem prime_reindex (f : Signature K n) (prime : Prime (⟨n,f⟩ : AnySignature K)) (e : Equiv.Perm (Fin n)) :
    Prime (⟨n,Tensor.reindex e f⟩ : AnySignature K) := by
  constructor
  · intro zero
    apply prime.1
    have h := congrArg (Tensor.reindex e.symm) zero
    rw [Tensor.reindex_symm] at h
    funext x
    exact congrFun h x
  · rintro ⟨a,b,⟨split⟩⟩
    apply prime.2
    refine ⟨a,b,⟨{
      left_pos := split.left_pos
      right_pos := split.right_pos
      ports := split.ports.trans e.symm
      scale := split.scale
      equation := ?_ }⟩⟩
    funext x
    have h := congrFun split.equation (fun i=>x (e.symm i))
    simpa only [Tensor.reindex,Equiv.symm_apply_apply,Equiv.trans_apply] using h

theorem normal_zero : T.normal (K:=K) 0 0 0 0=0 := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem signed_zero : S.signed (K:=K) 0 0 0=0 := by
  simpa only [S.signed,T.normal,neg_zero] using (normal_zero (K:=K))

theorem pair_det (A D : K) (prime : Prime (⟨4,T.normal A 0 0 D⟩ : AnySignature K)) : A^2≠D^2 := by
  intro squares
  by_cases ha : A=0
  · have hd : D=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa only [ha,zero_pow (by decide : (2:ℕ)≠0)] using squares.symm)
    apply prime.1
    rw [ha,hd,normal_zero]
  exact F.pair_not_prime A D ha squares prime

theorem eo_det (C D : K) (prime : Prime (⟨4,T.normal 0 0 C D⟩ : AnySignature K)) : C^2≠D^2 := by
  intro squares
  by_cases hc : C=0
  · have hd : D=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa only [hc,zero_pow (by decide : (2:ℕ)≠0)] using squares.symm)
    apply prime.1
    rw [hc,hd,normal_zero]
  exact F.eo_not_prime C D hc squares prime

theorem signed_sum (B C : K) (prime : Prime (⟨4,S.signed B C 0⟩ : AnySignature K)) : B^2+C^2≠0 := by
  intro sum
  by_cases hb : B=0
  · have hc : C=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa only [hb,zero_pow (by decide : (2:ℕ)≠0),zero_add] using sum)
    apply prime.1
    rw [hb,hc,signed_zero]
  exact F.signed_not_prime B C hb sum prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4PrimeTools
end
