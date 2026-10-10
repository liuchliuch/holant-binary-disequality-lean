import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseLargeOrder
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrders

/-! A literal finite port selection puts every nonempty sparse complementary
middle support into one or two live opposite pairs with b=y=0. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseCanonical
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export PaperTerminalBridgeDenseOrders (order reordered orderedEntries entries_reordered)
end O
namespace L
export PaperTerminalBridgeSparseOrders (MiddleLive)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def Rigid (e : Entries K) : Prop :=
  (e.b=0↔e.y=0) ∧ (e.c=0↔e.z=0) ∧ (e.d=0↔e.w=0) ∧
  (e.b≠0→e.c≠0→e.b*e.y=e.c*e.z) ∧
  (e.b≠0→e.d≠0→e.b*e.y=e.d*e.w) ∧
  (e.c≠0→e.d≠0→e.c*e.z=e.d*e.w)

def SomeZero (e : Entries K) : Prop := e.b=0 ∨ e.c=0 ∨ e.d=0 ∨ e.w=0 ∨ e.z=0 ∨ e.y=0

def Canonical (f : Signature K 4) : Prop :=
  (entries f).b=0 ∧ (entries f).y=0 ∧ (entries f).c≠0 ∧ (entries f).z≠0 ∧
    (((entries f).d=0 ∧ (entries f).w=0) ∨
      ((entries f).d≠0 ∧ (entries f).w≠0 ∧ (entries f).c*(entries f).z=(entries f).d*(entries f).w))

theorem rigid_reordered (f : Signature K 4) (h : Rigid (entries f)) (k : Fin 3) :
    Rigid (entries (O.reordered f k)) := by
  rcases h with ⟨b,c,d,bc,bd,cd⟩
  rw [O.entries_reordered]
  fin_cases k
  · exact ⟨b,c,d,bc,bd,cd⟩
  · exact ⟨c,b,d,fun hc hb=>(bc hb hc).symm,cd,bd⟩
  · exact ⟨d,c,b,fun hd hc=>(cd hc hd).symm,fun hd hb=>(bd hb hd).symm,
      fun hc hb=>(bc hb hc).symm⟩

theorem live_reordered (f : Signature K 4) (h : L.MiddleLive f) (k : Fin 3) : L.MiddleLive (O.reordered f k) := by
  fin_cases k <;> simp [L.MiddleLive,O.entries_reordered,O.orderedEntries] at * <;> tauto

theorem swap_entries (f : Signature K 4) : entries (Tensor.reindex (Equiv.swap (2 : Fin 4) 3) f)=
    ⟨(entries f).a,(entries f).b,(entries f).d,(entries f).c,
      (entries f).z,(entries f).w,(entries f).y,(entries f).x⟩ := by
  apply Entries.ext
  all_goals apply congrArg f
  all_goals funext i;fin_cases i <;> rfl

theorem source (f : Signature K 4) (rigid : Rigid (entries f))
    (zero : SomeZero (entries f)) (live : L.MiddleLive f) :
    ∃e : Equiv.Perm (Fin 4),Canonical (Tensor.reindex e f) := by
  have selected : ∃k : Fin 3,(entries (O.reordered f k)).b=0 := by
    rcases zero with b|c|d|w|z|y
    · exact ⟨0,by rw [O.entries_reordered];exact b⟩
    · exact ⟨1,by rw [O.entries_reordered];exact c⟩
    · exact ⟨2,by rw [O.entries_reordered];exact d⟩
    · exact ⟨2,by rw [O.entries_reordered];exact rigid.2.2.1.mpr w⟩
    · exact ⟨1,by rw [O.entries_reordered];exact rigid.2.1.mpr z⟩
    · exact ⟨0,by rw [O.entries_reordered];exact rigid.1.mpr y⟩
  obtain ⟨k,bzero⟩ := selected
  let g := O.reordered f k
  have rg := rigid_reordered f rigid k
  have lg := live_reordered f live k
  change Rigid (entries g) at rg
  change (entries g).b=0 at bzero
  have yzero : (entries g).y=0 := rg.1.mp bzero
  by_cases hc : (entries g).c≠0
  · refine ⟨O.order k,bzero,yzero,hc,?_,?_⟩
    · exact fun zero=>hc (rg.2.1.mpr zero)
    · by_cases hd : (entries g).d=0
      · exact Or.inl ⟨hd,rg.2.2.1.mp hd⟩
      · exact Or.inr ⟨hd,fun zero=>hd (rg.2.2.1.mpr zero),rg.2.2.2.2.2 hc hd⟩
  · have czero : (entries g).c=0 := not_ne_iff.mp hc
    have zzero : (entries g).z=0 := rg.2.1.mp czero
    have hd : (entries g).d≠0 := by
      intro dzero
      have wzero := rg.2.2.1.mp dzero
      change L.MiddleLive g at lg
      simp [L.MiddleLive,bzero,yzero,czero,zzero,dzero,wzero] at lg
    have hw : (entries g).w≠0 := fun zero=>hd (rg.2.2.1.mpr zero)
    refine ⟨(O.order k).trans (Equiv.swap 2 3),?_⟩
    change Canonical (Tensor.reindex (Equiv.swap (2 : Fin 4) 3) g)
    unfold Canonical
    rw [swap_entries]
    exact ⟨bzero,yzero,hd,hw,Or.inl ⟨czero,zzero⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseCanonical
end
