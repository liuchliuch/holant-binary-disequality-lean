import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseCancellation

/-! Three literal port orders cover every dense failure of equal opposite
products. This removes the selected-cut guard from the diagonal cancellation
source, while retaining the equal-product exceptional family explicitly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseOrders
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace D
export PaperTerminalBridgeDenseCancellation (dress cancellation)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def order : Fin 3→Equiv.Perm (Fin 4) := ![Equiv.refl _,Equiv.swap 1 2,Equiv.swap 1 3]
def reordered (f : Signature K 4) (k : Fin 3) : Signature K 4 := Tensor.reindex (order k) f

def orderedEntries (e : Entries K) : Fin 3→Entries K :=
  ![e,⟨e.a,e.c,e.b,e.d,e.w,e.y,e.z,e.x⟩,⟨e.a,e.d,e.c,e.b,e.y,e.z,e.w,e.x⟩]

theorem entries_reordered (f : Signature K 4) (k : Fin 3) :
    entries (reordered f k)=orderedEntries (entries f) k := by
  fin_cases k <;> apply Entries.ext
  all_goals apply congrArg f
  all_goals funext i;fin_cases i <;> rfl

theorem weight_order : ∀k : Fin 3,∀x : Fin 4→Bool,weight (fun i=>x (order k i))=weight x := by decide +kernel

theorem even_reordered (f : Signature K 4) (even : EvenSupport f) (k : Fin 3) : EvenSupport (reordered f k) := by
  intro x odd
  apply even
  rwa [weight_order]

theorem dense_reordered (f : Signature K 4) (dense : StableDenseParityAlgebra.Dense f) (k : Fin 3) :
    StableDenseParityAlgebra.Dense (reordered f k) := by
  unfold StableDenseParityAlgebra.Dense
  rw [entries_reordered]
  rcases dense with ⟨ha,hb,hc,hd,hw,hz,hy,hx⟩
  fin_cases k
  · exact ⟨ha,hb,hc,hd,hw,hz,hy,hx⟩
  · exact ⟨ha,hc,hb,hd,hw,hy,hz,hx⟩
  · exact ⟨ha,hd,hc,hb,hy,hz,hw,hx⟩

def EqualProducts (f : Signature K 4) : Prop :=
  (entries f).a*(entries f).x=(entries f).b*(entries f).y ∧
  (entries f).a*(entries f).x=(entries f).c*(entries f).z ∧
  (entries f).a*(entries f).x=(entries f).d*(entries f).w

theorem separated_order (f : Signature K 4) (different : ¬EqualProducts f) :
    ∃k : Fin 3,(entries (reordered f k)).a*(entries (reordered f k)).x≠
      (entries (reordered f k)).b*(entries (reordered f k)).y := by
  by_cases first : (entries f).a*(entries f).x=(entries f).b*(entries f).y
  · by_cases second : (entries f).a*(entries f).x=(entries f).c*(entries f).z
    · refine ⟨2,?_⟩
      rw [entries_reordered]
      change (entries f).a*(entries f).x≠(entries f).d*(entries f).w
      exact fun third=>different ⟨first,second,third⟩
    · refine ⟨1,?_⟩
      rw [entries_reordered]
      exact second
  · refine ⟨0,?_⟩
    rw [entries_reordered]
    exact first

theorem source (f : Signature K 4) (even : EvenSupport f) (dense : StableDenseParityAlgebra.Dense f)
    (different : ¬EqualProducts f) :
    ∃k : Fin 3,∃r t : K,r≠0 ∧ t≠0 ∧ (t=1 ∨ t=2 ∨ t=3) ∧
      EightVertexCancellationLocal.Applicable (D.dress (reordered f k) r t) := by
  obtain ⟨k,separate⟩ := separated_order f different
  obtain ⟨t,choice,ht,hr,applicable⟩ := D.cancellation (reordered f k)
    (even_reordered f even k) (dense_reordered f dense k) separate
  exact ⟨k,_,t,hr,ht,choice,applicable⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseOrders
end
