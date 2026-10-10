import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrderTwo

/-! Sparse large-order odd-cap rigidity over the actual complete complex
root deck. Column live counts force complementary zero patterns. Any two
live complementary middle pairs have the same opposite product. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseLargeOrder
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.Projective.CyclicPhasePencil
namespace P
export PaperTerminalBridgeFiniteCaps (Samples)
end P
namespace O
export PaperTerminalBridgeDenseOrders (order reordered entries_reordered)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false

def liveCount (z : ℂ) : ℕ := if z=0 then 0 else 1

theorem count_zero (z : ℂ) : liveCount z=0↔z=0 := by
  classical
  simp [liveCount]

theorem pencil_count {m : ℕ} (hm : 3≤m) (a b c d : ℂ)
    (samples : ∀t : ℂ,t^m=1→ScalarSample m (a+t*c) (b+t*d)) :
    liveCount a+liveCount c=liveCount b+liveCount d := by
  classical
  have hs : ScalarSamples m a (-c) (-b) d := by
    intro t ht
    simpa using samples t ht
  obtain ⟨α,root,h|h|h⟩ := relation_of_samples hm a (-c) (-b) d hs
  all_goals have nonzero : α≠0 := root_ne_zero (by omega) root
  · have hb : b=α*a := by linear_combination -h.1
    have hd : d=α*c := by simpa using h.2
    rw [hb,hd]
    simp [liveCount,nonzero]
  · have hc : c=0 := neg_eq_zero.mp h.1
    have hb : b=0 := neg_eq_zero.mp h.2.1
    rw [hc,hb,h.2.2]
    simp [liveCount,nonzero]
  · have hb : b=α*c := by linear_combination -h.2.2
    rw [h.1,h.2.1,hb]
    simp [liveCount,nonzero]

theorem zero_patterns {m : ℕ} (hm : 3≤m) (e : Entries ℂ) (samples : P.Samples m e) :
    (e.b=0↔e.y=0) ∧ (e.c=0↔e.z=0) ∧ (e.d=0↔e.w=0) := by
  have first := pencil_count hm e.w e.z e.c e.d samples.first
  have second := pencil_count hm e.w e.y e.b e.d samples.second
  have opposite := pencil_count hm e.c e.w e.d e.z samples.opposite
  have cb : liveCount e.c=liveCount e.z := by omega
  have db : liveCount e.d=liveCount e.w := by omega
  have bb : liveCount e.b=liveCount e.y := by omega
  exact ⟨by rw [←count_zero,←count_zero,bb],by rw [←count_zero,←count_zero,cb],
    by rw [←count_zero,←count_zero,db]⟩

theorem source {m : ℕ} (hm : 3≤m) (f : Signature ℂ 4)
    (samples : ∀e : Equiv.Perm (Fin 4),P.Samples m (entries (Tensor.reindex e f))) :
    ((entries f).b=0↔(entries f).y=0) ∧
    ((entries f).c=0↔(entries f).z=0) ∧
    ((entries f).d=0↔(entries f).w=0) ∧
    ((entries f).b≠0→(entries f).c≠0→(entries f).b*(entries f).y=(entries f).c*(entries f).z) ∧
    ((entries f).b≠0→(entries f).d≠0→(entries f).b*(entries f).y=(entries f).d*(entries f).w) ∧
    ((entries f).c≠0→(entries f).d≠0→(entries f).c*(entries f).z=(entries f).d*(entries f).w) := by
  let e := entries f
  have base : P.Samples m e := by simpa [Tensor.reindex] using samples (Equiv.refl _)
  have zeros := zero_patterns hm e base
  have changed := samples (O.order 2)
  change P.Samples m (entries (O.reordered f 2)) at changed
  rw [O.entries_reordered] at changed
  refine ⟨zeros.1,zeros.2.1,zeros.2.2,?_,?_,?_⟩
  · intro hb hc
    have hy : e.y≠0 := fun hz=>hb (zeros.1.mpr hz)
    obtain ⟨α,_root,hz,hb'⟩ := StableDenseResidualPencil.dense_scalar_pencil hm e.y e.z e.c e.b
      hy hc changed.first
    change e.b*e.y=e.c*e.z
    rw [hz,hb']
    ring
  · intro hb hd
    have hw : e.w≠0 := fun hz=>hd (zeros.2.2.mpr hz)
    obtain ⟨α,_root,hy,hd'⟩ := StableDenseResidualPencil.dense_scalar_pencil hm e.w e.y e.b e.d
      hw hb base.second
    change e.b*e.y=e.d*e.w
    rw [hy,hd']
    ring
  · intro hc hd
    have hw : e.w≠0 := fun hz=>hd (zeros.2.2.mpr hz)
    obtain ⟨α,_root,hz,hd'⟩ := StableDenseResidualPencil.dense_scalar_pencil hm e.w e.z e.c e.d
      hw hc base.first
    change e.c*e.z=e.d*e.w
    rw [hz,hd']
    ring


theorem mapped {K : Type} [Field K] (φ : K→+*ℂ) {m : ℕ} (hm : 3≤m) (f : Signature K 4)
    (samples : ∀e : Equiv.Perm (Fin 4),P.Samples m (entries (Tensor.reindex e (fun x=>φ (f x))))) :
    ((entries f).b=0↔(entries f).y=0) ∧
    ((entries f).c=0↔(entries f).z=0) ∧
    ((entries f).d=0↔(entries f).w=0) ∧
    ((entries f).b≠0→(entries f).c≠0→(entries f).b*(entries f).y=(entries f).c*(entries f).z) ∧
    ((entries f).b≠0→(entries f).d≠0→(entries f).b*(entries f).y=(entries f).d*(entries f).w) ∧
    ((entries f).c≠0→(entries f).d≠0→(entries f).c*(entries f).z=(entries f).d*(entries f).w) := by
  simpa only [entries,map_eq_zero,map_ne_zero,←map_mul,φ.injective.eq_iff] using source hm (fun x=>φ (f x)) samples


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseLargeOrder
end
