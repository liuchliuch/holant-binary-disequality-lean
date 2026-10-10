import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CurrentComplement
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatNonzero

/-! Genuine odd descent through the current raw deck. The six literal I/X
pair contractions have zero common kernel, so every nonzero odd row above
arity one supplies a smaller actual nonflat odd row. Only actual retained I
and residual torsion are used, not cardinality two or an odd-output handler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OddDescent
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
namespace R
export GlobalCloseCompletionC2ContractionReconstruction (pairSum zero_of_pair_sums)
end R
namespace C
export GlobalCloseCompletionC2CurrentComplement (first_pairSum pairSum_reindex kernel_member)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)

include torsion hI in
theorem raw_live {m : ℕ} (f : Signature K (m+3)) (nonzero : f≠0) :
    ∃key : RawCardKey (m+1) (completeGroup F torsion),rawCard F torsion f key≠0 := by
  classical
  by_contra! zero
  have ordered (e : Equiv.Perm (Fin (m+3))) (p : Bool) :
      Signature.contract (ClosureSourceRows.originalC2Binary p) (Tensor.reindex e.symm f)=0 := by
    obtain ⟨key,c,_,equation⟩ := DeckContraction.orderedClosure_raw_scalar F torsion hI f e
      (ClosureSourceRows.originalC2Binary p) (C.kernel_member F torsion hI p)
    rw [equation,zero,smul_zero]
  have pair (e : Equiv.Perm (Fin (m+3))) (w : Fin (m+3)→Bool) :
      R.pairSum f (e 0) (e 1) w=0 := by
    rw [←C.pairSum_reindex f e 0 1 w,C.first_pairSum]
    exact congrFun (ordered e _) _
  have h2 : 2 % (m+3)=2 := Nat.mod_eq_of_lt (by omega)
  apply nonzero
  apply R.zero_of_pair_sums f 0 1 2
  · exact pair (Equiv.refl _)
  · intro w
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using pair (Equiv.swap (1 : Fin (m+3)) 2) w
  · intro w
    simpa [Equiv.swap_apply_def,Fin.ext_iff,h2] using pair
      ((Equiv.swap (0 : Fin (m+3)) 1).trans (Equiv.swap 0 2)) w

theorem odd_nonflat {n : ℕ} (phi : K→+*ℂ) (f : Signature K n) (nonzero : f≠0) (odd : Odd n) :
    ¬FlatOrZero (RingHomRealization.mapSignature phi f) := by
  rintro (zero|⟨_,_,D,selfdual,_⟩)
  · apply nonzero
    funext x
    apply phi.injective
    have h := congrFun zero x
    simpa only [RingHomRealization.mapSignature,Pi.zero_apply,map_zero] using h
  · exact (Nat.not_even_iff_odd.mpr odd) (selfDual_arity_even D selfdual)

include torsion hI in
theorem smaller {m : ℕ} (phi : K→+*ℂ) (f : Signature K (m+3))
    (actual : Gadget.Realizes F .disequality f) (nonzero : f≠0) (odd : Odd (m+3)) :
    ∃q : Signature K (m+1),Gadget.Realizes F .disequality q ∧
      ¬FlatOrZero (RingHomRealization.mapSignature phi q) := by
  obtain ⟨key,live⟩ := raw_live F torsion hI f nonzero
  refine ⟨rawCard F torsion f key,rawCard_realizes_exact F torsion hI (by norm_num) f actual key,?_⟩
  apply odd_nonflat phi _ live
  obtain ⟨k,hk⟩ := odd
  exact ⟨k-1,by omega⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OddDescent
end
