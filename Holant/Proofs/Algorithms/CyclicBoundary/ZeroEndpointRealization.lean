import Holant.Proofs.Algorithms.CyclicBoundary.PhysicalAttachments
import Holant.Proofs.Algorithms.CyclicBoundary.TwoCopyTransport
import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointAlternative


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointRealization
open Holant.Certificates.FourthRootOdd Holant.Certificates.TwelveLoops
open TwoCopyKernels TwoCopyTransport ZeroEndpointFactor ZeroEndpointJoin
open ZeroEndpointDressing PhysicalAttachments
noncomputable section

def internalPhases (p : Fin 6) (s t : ℂ) : Fin 4 → ℂ :=
  fun i => ![s,t,1,1] ((portEquiv p).symm i)

theorem internal_roots (p : Fin 6) {N : ℕ} {s t : ℂ}
    (hs : s^N=1) (ht : t^N=1) : ∀ i, (internalPhases p s t i)^N=1 := by
  intro i
  fin_cases p <;> fin_cases i <;>
    simp [internalPhases,portEquiv,portInverse,hs,ht]

theorem dress_insertPair (g : Signature ℂ 4) (p : Fin 6) (s t : ℂ)
    (u v : Bool) (x : Fin 2 → Bool) :
    dress g (internalPhases p s t) (insertPair p u v x) =
      g (insertPair p u v x) * (s^(if u then 1 else 0)*t^(if v then 1 else 0)) := by
  unfold dress
  congr 1
  fin_cases p <;> cases u <;> cases v <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [internalPhases,insertPair,portEquiv,portInverse,Fin.prod_univ_succ,h0,h1]

/-- A phase is attached only to the second endpoint of each internal native
edge. Its contribution multiplies that edge's corresponding TwoCopyKernels.diagonal entry. -/
theorem internal_contraction (f g : Signature ℂ 4) (p : Fin 6) (s t : ℂ) :
    contraction f (dress g (internalPhases p s t)) p (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1)) =
      contraction f g p (TwoCopyKernels.diagonal 1 (-s)) (TwoCopyKernels.diagonal 1 (-t)) := by
  funext x
  simp [contraction,dress_insertPair,TwoCopyKernels.diagonal]
  ring

theorem native_hadamard_edge :
    Kernel.pullback (Signature.disequality : Kernel ℂ) hadamard =
      (2:ℂ) • TwoCopyKernels.diagonal 1 (-1) := by
  funext u v
  cases u <;> cases v <;>
    norm_num [Kernel.pullback,Kernel.mul,Kernel.transpose,hadamard,
      Signature.disequality,TwoCopyKernels.diagonal]

/-- Both native edges contribute their factor 2. Boundary coordinates are
the original physical Hadamard action, left explicitly on the resulting tensor. -/
theorem native_internal_formula (f g : Signature ℂ 4) (p : Fin 6) (s t : ℂ) :
    contraction (physical f) (physical (dress g (internalPhases p s t))) p
      Signature.disequality Signature.disequality =
      (4:ℂ) • physical (contraction f g p (TwoCopyKernels.diagonal 1 (-s)) (TwoCopyKernels.diagonal 1 (-t))) := by
  unfold physical
  rw [contraction_action,native_hadamard_edge]
  have he := contraction_scales 1 1 2 2 f (dress g (internalPhases p s t)) p
    (TwoCopyKernels.diagonal 1 (-1)) (TwoCopyKernels.diagonal 1 (-1))
  simp only [one_smul] at he
  norm_num at he
  rw [he,internal_contraction,action_scale]

theorem diagonal_neg_neg_one : (TwoCopyKernels.diagonal 1 (-(-1:ℂ))) = Signature.equality := by
  funext u v
  cases u <;> cases v <;> simp [TwoCopyKernels.diagonal,Signature.equality]

/-- Exact source-family realizability up to a recorded nonzero scalar, before
the final four boundary phases. No factor-extraction reduction is used here. -/
theorem zero_join_upTo {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (r a : Fin 3 → ℂ)
    (ha : ∀ k, (a k)^N=1) (hN : Even N)
    (hq : Gadget.RealizesUpTo F .disequality (physical (table r a))) (i : Fin 3) :
    Gadget.RealizesUpTo F .disequality (physical (join r a i).denote) := by
  let s := a (other₁ i)*a (other₂ i)
  have hs : s^N=1 := by simp [s,mul_pow,ha]
  have ht : (-1:ℂ)^N=1 := by simp [hN.neg_pow]
  have hg := phase_dressing_upTo R (table r a) hq
    (internalPhases (selected i) s (-1)) (internal_roots (selected i) hs ht)
  have hn := native_realizesUpTo F _ _ hq hg (selected i) (by norm_num)
  rw [native_internal_formula,diagonal_neg_neg_one] at hn
  have hj : contraction (table r a) (table r a) (selected i)
      (TwoCopyKernels.diagonal 1 (-s)) Signature.equality = (join r a i).denote := by
    rw [join,network_denote]
  rw [hj] at hn
  exact upTo_of_scale _ 4 (by norm_num) hn

/-- The same retained binary representatives implement the final boundary
phases. The output tensor is precisely the one whose full table and genuine
tensor-primality were computed in ZeroEndpointDressing and SupportPrime. -/
theorem dressed_zero_join_upTo {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (r a : Fin 3 → ℂ)
    (ha : ∀ k, (a k)^N=1) (hN : Even N)
    (hq : Gadget.RealizesUpTo F .disequality (physical (table r a))) (i : Fin 3) :
    Gadget.RealizesUpTo F .disequality
      (physical (dress (join r a i).denote (phases a i))) :=
  phase_dressing_upTo R _ (zero_join_upTo R r a ha hN hq i) _
    (phases_are_roots a i hN ha)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointRealization
