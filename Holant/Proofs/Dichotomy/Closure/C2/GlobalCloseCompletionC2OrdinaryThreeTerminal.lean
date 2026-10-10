import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryDenseTerminal
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySeparatedCaps
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySquare

/-! Complete three-live-coefficient consumer. The Eq4 separating graph and
the scalar-X cap graph may use different original port orders. A zero endpoint
is removed by an actual two-copy parity-block square with nonzero entries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryThreeTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z paired_squares)
end T
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc swap_bd)
end O
namespace S
export GlobalCloseCompletionC2OrdinarySquare (square square_normal)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

include back zLiteral in
theorem endpoint_live (N : Macro H 4) (A B C D : K) (hA : A≠0) (hC : C≠0) (hD : D≠0)
    (form : N.network.denote=T.normal A B C D) :
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨
      OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
  by_cases hB : B≠0
  · exact GlobalCloseCompletionC2OrdinaryDenseTerminal.classified G K F H back N A B C D hA hB hC hD form z zLiteral
  have zero : B=0 := not_not.mp hB
  have sep : ∃Q : Macro H 4,∃u v w t : K,Q.network.denote=T.normal u v w t ∧ (u^2-v^2)^2≠(w^2-t^2)^2 := by
    by_cases h0 : (A^2-B^2)^2≠(C^2-D^2)^2
    · exact ⟨N,A,B,C,D,form,h0⟩
    by_cases h1 : (A^2-C^2)^2≠(B^2-D^2)^2
    · exact ⟨N.reindex (Equiv.swap 1 2),A,C,B,D,by rw [Macro.reindex_denote,form,O.swap_bc],h1⟩
    by_cases h2 : (A^2-D^2)^2≠(B^2-C^2)^2
    · refine ⟨N.reindex (Equiv.swap 1 3),A,D,C,B,by rw [Macro.reindex_denote,form,O.swap_bd],?_⟩
      intro eqn
      apply h2
      exact eqn.trans (by ring)
    have pairs := T.paired_squares A B C D (not_not.mp h0) (not_not.mp h1) (not_not.mp h2) (by norm_num)
    rcases pairs with h|h|h
    · exact False.elim ((pow_ne_zero 2 hA) (by simpa [zero] using h.1))
    · exact False.elim ((pow_ne_zero 2 hD) (by simpa [zero] using h.2.symm))
    · exact False.elim ((pow_ne_zero 2 hC) (by simpa [zero] using h.2.symm))
  obtain ⟨Q,u,v,w,t,hQ,sep⟩ := sep
  let input : GlobalCloseCompletionC2OrdinarySeparated.Input G := {
    K := K
    degree := degree
    F := F
    count := r
    b := b
    H := H
    graph := Q.network
    labels := Q.labels
    exact := Q.exact
    ordinary := Q.edges
    zLabel := z
    z := 1
    zNonzero := one_ne_zero
    zLiteral := by exact zLiteral.trans (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
          (by funext x; change T.Z (x 0) (x 1)=1*T.Z (x 0) (x 1); rw [one_mul]))
    a := u
    b0 := v
    c := w
    d := t
    form := hQ
    separated := sep
    toOriginal := back }
  exact GlobalCloseCompletionC2OrdinarySeparatedCaps.classified G input N A B C D hA hC hD form

include back zLiteral in
theorem zero_endpoint (N : Macro H 4) (B C D : K) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (form : N.network.denote=T.normal 0 B C D) :
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨
      OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
  have finish (Q : Macro H 4) (u v w : K) (hu : u≠0) (hv : v≠0) (hw : w≠0)
      (hs : v^2+w^2≠0) (hq : Q.network.denote=T.normal 0 u v w) :
      Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨
        OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
    apply endpoint_live G K F H back z zLiteral (S.square H Q) (u^2) 0 (v^2+w^2) (2*v*w)
      (pow_ne_zero _ hu) hs (mul_ne_zero (mul_ne_zero (by norm_num) hv) hw)
    simpa using S.square_normal H Q 0 u v w hq
  by_cases h0 : C^2+D^2≠0
  · exact finish N B C D hB hC hD h0 form
  by_cases h1 : B^2+D^2≠0
  · exact finish (N.reindex (Equiv.swap 1 2)) C B D hC hB hD h1
      (by rw [Macro.reindex_denote,form,O.swap_bc])
  have h2 : C^2+B^2≠0 := by
    intro zero
    have live : (2:K)*D^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hD)
    apply live
    linear_combination (not_not.mp h0)+(not_not.mp h1)-zero
  exact finish (N.reindex (Equiv.swap 1 3)) D C B hD hC hB h2
    (by rw [Macro.reindex_denote,form,O.swap_bd])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryThreeTerminal
end
