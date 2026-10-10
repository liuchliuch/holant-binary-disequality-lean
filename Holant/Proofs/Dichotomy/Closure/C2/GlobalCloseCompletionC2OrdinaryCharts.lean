import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryShape

/-! The eight checked charts are actual source graphs. Port reindexing and a
retained literal Z vertex suffice; Affine conclusions are pulled back through
those exact reversible coordinate operations. All other conclusions concern
the unchanged whole original ordinary table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryCharts
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z)
end T
namespace C
export GlobalCloseCompletionC2Q4Charts (phase flip permutation chart Shape)
end C
namespace Q
export GlobalCloseCompletionC2OrdinaryQuaternary (Outcome reindex_back)
end Q
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (phase)
end O
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (attach_denote)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem phase_involutive (b : Bool) (f : Signature AlgebraicComplex 4) : C.phase b (C.phase b f)=f := by
  funext x
  cases b <;> cases h0 : x 0 <;> simp [C.phase,h0]

theorem phase_affine (b : Bool) (f : Signature AlgebraicComplex 4) (hf : Affine f) : Affine (C.phase b f) := by
  cases b
  · have eqn : C.phase false f=f := by funext x; simp [C.phase]
    rw [eqn]
    exact hf
  · have h := GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers (0 : Fin 4) 1 (-1) one_ne_zero (by norm_num)
    exact h.mul hf

theorem phase_affine_iff (b : Bool) (f : Signature AlgebraicComplex 4) : Affine (C.phase b f) ↔ Affine f :=
  ⟨fun h=>by simpa only [phase_involutive] using phase_affine b _ h,phase_affine b f⟩

variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (z : Fin r) (literal : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

def phaseMacro (choice : Bool) (N : Macro H 4) : Macro H 4 := if choice then O.phase H z literal N 0 else N

theorem phaseMacro_denote (choice : Bool) (N : Macro H 4) :
    (phaseMacro K H z literal choice N).network.denote=fun x=>(if choice && x 0 then -1 else 1)*N.network.denote x := by
  cases choice
  · funext x; simp [phaseMacro]
  · change (GlobalCloseCompletionKleinOrdinaryAttach.attach N.network 0 T.Z).denote=_
    rw [A.attach_denote]
    funext x
    cases h0 : x 0 <;> simp [T.Z,Holant.Certificates.EqualityQuaternary.Klein.Orbit.site,h0]
    all_goals
      apply congrArg N.network.denote
      rw [←h0]
      exact Function.update_eq_self 0 x

theorem mapped_phase (choice : Bool) (N : Macro H 4) :
    RingHomRealization.mapSignature K.subtype (phaseMacro K H z literal choice N).network.denote=
      C.phase choice (RingHomRealization.mapSignature K.subtype N.network.denote) := by
  rw [phaseMacro_denote]
  funext x
  cases choice <;> cases h0 : x 0 <;> simp [RingHomRealization.mapSignature,C.phase,h0]

include back literal in
theorem phase_back (choice : Bool) (N : Macro H 4)
    (h : Q.Outcome G K H (phaseMacro K H z literal choice N)) : Q.Outcome G K H N := by
  rcases h with h|h
  · left
    rw [mapped_phase] at h
    exact (phase_affine_iff choice _).mp h
  · exact Or.inr h

def chartMacro (j : Fin 8) (N : Macro H 4) : Macro H 4 :=
  phaseMacro K H z literal (C.flip j) (N.reindex (C.permutation j))

theorem mapped_chart (j : Fin 8) (N : Macro H 4) (v : Fin 8→AlgebraicComplex)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote=
      sourceKBasis.action (GlobalCloseCompletionC2Q4UnionCurrent.tensor v)) :
    RingHomRealization.mapSignature K.subtype (chartMacro K H z literal j N).network.denote=C.chart j v := by
  rw [chartMacro,mapped_phase]
  have reindexed : RingHomRealization.mapSignature K.subtype (N.reindex (C.permutation j)).network.denote=
      Tensor.reindex (C.permutation j) (RingHomRealization.mapSignature K.subtype N.network.denote) := by
    rw [Macro.reindex_denote]
    rfl
  rw [reindexed,form]
  rfl

include back literal in
theorem classified (N : Macro H 4) (v : Fin 8→AlgebraicComplex)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote=
      sourceKBasis.action (GlobalCloseCompletionC2Q4UnionCurrent.tensor v))
    (accepted : GlobalCloseCompletionC2Q4Union.Accepted (fun i=>(v i:ℂ))) : Q.Outcome G K H N := by
  obtain ⟨j,shape⟩ := GlobalCloseCompletionC2Q4Charts.accepted_chart v accepted
  have h := GlobalCloseCompletionC2OrdinaryShape.classified G K F H back z literal
    (chartMacro K H z literal j N) (by rw [mapped_chart K H z literal j N v form];exact shape)
  apply Q.reindex_back G K H N (C.permutation j)
  exact phase_back G K F H back z literal (C.flip j) (N.reindex (C.permutation j)) h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryCharts
end
