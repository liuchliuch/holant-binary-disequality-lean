import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOddCards

/-! Actual finite native antidiagonal closure supplies the reduced deck.
The finite cyclic order and every phase representative are derived from the
original number-field gadgets. One-sided and infinite-ratio outputs are the
explicit alternative branches, not hidden premises of a final dichotomy. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeFiniteDeck
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Projective.CyclicPhasePencil
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace A
export PaperTerminalBridgeAntiGroup (Available complete complete_mapped)
end A
namespace O
export PaperTerminalBridgeOddCards (pencil actual_pencil)
end O
namespace P
export PaperTerminalBridgeFiniteCaps (Samples MiddleProducts order_one order_two large_order)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def NoOneSided (F : SignatureFamily K) : Prop :=
  ∀p q : K,Gadget.RealizesUpTo F .disequality (C.antiTensor p q)→(p=0↔q=0)

theorem ratio_actual (F : SignatureFamily K) (p q : K) (hp : p≠0)
    (actual : Gadget.RealizesUpTo F .disequality (C.antiTensor p q)) : A.Available F (q/p) := by
  apply PaperTerminalBridgeEqualProductsCaps.unscale F (C.antiTensor 1 (q/p)) p hp
  have value : (fun x=>p*C.antiTensor 1 (q/p) x)=C.antiTensor p q := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.antiTensor,h0,h1,hp] <;> field_simp
  rwa [value]

theorem sample (F : SignatureFamily K) (φ : K→+*ℂ) (m : ℕ)
    (safe : NoOneSided F)
    (root : ∀t : K,t≠0→A.Available F t→φ t^m=1)
    (p q : K) (actual : Gadget.RealizesUpTo F .disequality (C.antiTensor p q)) :
    ScalarSample m (φ p) (φ q) := by
  by_cases hp : p=0
  · exact Or.inl ⟨by rw [hp,map_zero],by rw [(safe p q actual).mp hp,map_zero]⟩
  · have hq : q≠0 := fun hz=>hp ((safe p q actual).mpr hz)
    refine Or.inr ⟨(map_ne_zero φ).mpr hp,(map_ne_zero φ).mpr hq,?_⟩
    simpa only [map_div₀] using root (q/p) (div_ne_zero hq hp) (ratio_actual F p q hp actual)

theorem pencil_map (φ : K→+*ℂ) (f : Signature K 4) (k : Fin 3) (t : K) :
    O.pencil (entries (fun x=>φ (f x))) k (φ t)=
      (φ (O.pencil (entries f) k t).1,φ (O.pencil (entries f) k t).2) := by
  fin_cases k <;> simp [O.pencil,entries,map_add,map_mul]

variable [NumberField K]

theorem source (F : SignatureFamily K) (φ : K→+*ℂ) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (safe : NoOneSided F)
    (torsion : ∀t : K,A.Available F t→t≠0→IsOfFinOrder t) :
    ∃m : ℕ,0<m ∧ P.Samples m (entries (fun x=>φ (f x))) := by
  obtain ⟨m,positive,root,cover⟩ := A.complete_mapped F φ torsion
  have all (k : Fin 3) (z : ℂ) (hz : z^m=1) :
      ScalarSample m (O.pencil (entries (fun x=>φ (f x))) k z).1
        (O.pencil (entries (fun x=>φ (f x))) k z).2 := by
    obtain ⟨t,_nonzero,phase,rfl⟩ := cover z hz
    rw [pencil_map]
    exact sample F φ m safe root _ _ (O.actual_pencil F f actual even k t phase)
  exact ⟨m,positive,⟨all 0,all 1,all 2⟩⟩

theorem classification (F : SignatureFamily K) (φ : K→+*ℂ) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (dense : StableDenseParityAlgebra.Dense f) (safe : NoOneSided F)
    (torsion : ∀t : K,A.Available F t→t≠0→IsOfFinOrder t) :
    P.MiddleProducts (entries f) ∨
      ∃ε : K,ε^2=1 ∧ (entries f).b=ε*(entries f).y ∧
        (entries f).c=ε*(entries f).z ∧ (entries f).d=ε*(entries f).w := by
  obtain ⟨m,positive,samples⟩ := source F φ f actual even safe torsion
  let e := entries f
  have hw : e.w≠0 := dense.2.2.2.2.1
  have hz : e.z≠0 := dense.2.2.2.2.2.1
  have hb : e.b≠0 := dense.2.1
  have hc : e.c≠0 := dense.2.2.1
  by_cases one : m=1
  · subst m
    obtain ⟨b,c,d⟩ := P.order_one _ samples
    right
    refine ⟨1,by simp,?_,?_,?_⟩
    · simpa [e,entries] using φ.injective b
    · simpa [e,entries] using φ.injective c
    · simpa [e,entries] using φ.injective d
  by_cases two : m=2
  · subst m
    obtain ⟨ε,square,b,c,d⟩ := P.order_two _ ((map_ne_zero φ).mpr hw) ((map_ne_zero φ).mpr hz) samples
    have value : ε=φ (e.c/e.z) := by
      rw [map_div₀]
      apply (eq_div_iff ((map_ne_zero φ).mpr hz)).mpr
      exact c.symm
    rw [value] at square b c d
    right
    refine ⟨e.c/e.z,φ.injective ?_,φ.injective ?_,φ.injective ?_,φ.injective ?_⟩
    · simpa only [map_pow,map_one] using square
    · simpa only [map_mul,entries] using b
    · simpa only [map_mul,entries] using c
    · simpa only [map_mul,entries] using d
  · have large : 3≤m := by omega
    obtain ⟨first,second⟩ := P.large_order large _ ((map_ne_zero φ).mpr hw)
      ((map_ne_zero φ).mpr hb) ((map_ne_zero φ).mpr hc) samples
    left
    constructor
    · apply φ.injective
      simpa only [map_mul,entries] using first
    · apply φ.injective
      simpa only [map_mul,entries] using second


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeFiniteDeck
end
