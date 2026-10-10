import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeFiniteDeck
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrderTwo

/-! One exact actual cyclic order supplies the odd-card samples in every
port order simultaneously. No density premise is used. The same scalar
sample is faithfully recovered in the original field for orders one/two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrderTwoDeck
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.Projective.CyclicPhasePencil
namespace A
export PaperTerminalBridgeAntiGroup (Available complete_mapped)
end A
namespace D
export PaperTerminalBridgeFiniteDeck (NoOneSided sample pencil_map)
end D
namespace O
export PaperTerminalBridgeOddCards (pencil actual_pencil)
end O
namespace P
export PaperTerminalBridgeFiniteCaps (Samples)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem even_reindex (f : Signature K 4) (even : EvenSupport f) (e : Equiv.Perm (Fin 4)) :
    EvenSupport (Tensor.reindex e f) := by
  intro x odd
  apply even
  have weightEq : weight (fun i=>x (e i))=weight x := Equiv.sum_comp e (fun i=>if x i then 1 else 0)
  rwa [weightEq]

theorem sample_descend (φ : K→+*ℂ) (m : ℕ) (p q : K)
    (h : ScalarSample m (φ p) (φ q)) : ScalarSample m p q := by
  rcases h with ⟨hp,hq⟩ | ⟨hp,hq,root⟩
  · exact Or.inl ⟨(map_eq_zero φ).mp hp,(map_eq_zero φ).mp hq⟩
  · refine Or.inr ⟨(map_ne_zero φ).mp hp,(map_ne_zero φ).mp hq,φ.injective ?_⟩
    simpa only [map_pow,map_div₀,map_one] using root

theorem samples_descend (φ : K→+*ℂ) (m : ℕ) (f : Signature K 4)
    (samples : P.Samples m (entries (fun x=>φ (f x)))) : P.Samples m (entries f) := by
  have root (t : K) (h : t^m=1) : φ t^m=1 := by simpa only [map_pow,map_one] using congrArg φ h
  constructor
  · intro t h
    apply sample_descend φ m
    simpa only [map_add,map_mul,entries] using samples.first (φ t) (root t h)
  · intro t h
    apply sample_descend φ m
    simpa only [map_add,map_mul,entries] using samples.second (φ t) (root t h)
  · intro t h
    apply sample_descend φ m
    simpa only [map_add,map_mul,entries] using samples.opposite (φ t) (root t h)

variable [NumberField K]

theorem source (F : SignatureFamily K) (φ : K→+*ℂ) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (safe : D.NoOneSided F)
    (torsion : ∀t : K,A.Available F t→t≠0→IsOfFinOrder t) :
    ∃m : ℕ,0<m ∧
      (∀e : Equiv.Perm (Fin 4),P.Samples m (entries (Tensor.reindex e (fun x=>φ (f x))))) ∧
      (∀e : Equiv.Perm (Fin 4),P.Samples m (entries (Tensor.reindex e f))) := by
  obtain ⟨m,positive,root,cover⟩ := A.complete_mapped F φ torsion
  have all (e : Equiv.Perm (Fin 4)) : P.Samples m (entries (Tensor.reindex e (fun x=>φ (f x)))) := by
    let f' := Tensor.reindex e f
    have actual' : Gadget.Realizes F .disequality f' := by
      have h := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual e.symm
      simpa only [Equiv.symm_symm] using h
    have samples (k : Fin 3) (z : ℂ) (hz : z^m=1) :
        ScalarSample m (O.pencil (entries (fun x=>φ (f' x))) k z).1
          (O.pencil (entries (fun x=>φ (f' x))) k z).2 := by
      obtain ⟨t,_nonzero,phase,rfl⟩ := cover z hz
      rw [D.pencil_map]
      exact D.sample F φ m safe root _ _
        (O.actual_pencil F f' actual' (even_reindex f even e) k t phase)
    exact ⟨samples 0,samples 1,samples 2⟩
  exact ⟨m,positive,all,fun e=>samples_descend φ m (Tensor.reindex e f) (all e)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseOrderTwoDeck
end
