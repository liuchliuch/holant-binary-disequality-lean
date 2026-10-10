import Holant.Proofs.Traversal.ArityTwo.Descriptors
import Holant.Proofs.Traversal.ArityTwo.WalkTrace


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors
open Holant Holant.Complexity PortWalk
variable {s b : ℕ} {arity : ℕ → ℕ} {A : Type}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (vertex : ∀ v : Fin r.vertices.length, (Fin (degree (arity := arity) r v) → Bool) → A)
variable (edge : Fin r.edges.length → Kernel A)

theorem pathMatrices_trace (hd : ∀ v, degree (arity := arity) r v ≤ 2)
    {p q : r.Ports arity} {xs : List (r.Ports arity)} (ht : Trace r h p xs (.terminal q)) :
    ∃ ms right, pathMatrices r h vertex edge xs = some (ms,right) := by
  have aux : ∀ {p xs stop}, Trace r h p xs stop → ∀ q, stop = .terminal q →
      ∃ ms right, pathMatrices r h vertex edge xs = some (ms,right) := by
    intro p xs stop ht
    induction ht with
    | terminal p ho =>
      intro q he
      have hp := terminal_unary r hd p ho
      exact ⟨[],unaryTable r vertex p.1,by simp [pathMatrices,hp]⟩
    | repeated p => intro q he; cases he
    | step p out xs stop ho ht ih =>
      intro q he
      obtain ⟨ms,right,hm⟩ := ih q he
      have hp : degree (arity := arity) r p.1 ≠ 1 := by have hb := (other_some r p out ho).2.2; omega
      exact ⟨binaryTable r vertex p :: edgeTable r h edge out :: ms,right,by simp [pathMatrices,hp,ho,hm]⟩
  exact aux ht q rfl

theorem cycleMatrices_trace {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.repeated q)) : ∃ ms, cycleMatrices r h vertex edge xs = some ms := by
  have aux : ∀ {p xs stop}, Trace r h p xs stop → ∀ q, stop = .repeated q →
      ∃ ms, cycleMatrices r h vertex edge xs = some ms := by
    intro p xs stop ht
    induction ht with
    | terminal p ho => intro q he; cases he
    | repeated p => intro q he; exact ⟨[],rfl⟩
    | step p out xs stop ho ht ih =>
      intro q he
      obtain ⟨ms,hm⟩ := ih q he
      exact ⟨binaryTable r vertex p :: edgeTable r h edge out :: ms,by simp [cycleMatrices,ho,hm]⟩
  exact aux ht q rfl

theorem pathFrom_total (hd : ∀ v, degree (arity := arity) r v ≤ 2) (v : Fin r.vertices.length)
    (hv : degree (arity := arity) r v = 1) : ∃ c, pathFrom r h vertex edge v hv = some c := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 1 at hv; omega⟩⟩
  obtain ⟨q,hq,hqu⟩ := (path_completion r h hd p hv).1
  have ht := walk_trace r h (fuel r) [p] (cross r h p) (walk_not_exhausted r h _ _)
  change (walk r h (fuel r) [p] (cross r h p)).2 = .terminal q at hq
  rw [hq] at ht
  obtain ⟨ms,right,hm⟩ := pathMatrices_trace r h vertex edge hd ht
  refine ⟨.path (unaryTable r vertex v) (edgeTable r h edge p::ms) right,?_⟩
  simp only [pathFrom, p, hq, hm]
  rfl

theorem cycleFrom_total (hd : ∀ v, degree (arity := arity) r v ≤ 2) (v : Fin r.vertices.length)
    (hv : degree (arity := arity) r v = 2)
    (hu : ∀ w, (r.graph h).label w = (r.graph h).label v → degree (arity := arity) r w ≠ 1) :
    ∃ c, cycleFrom r h vertex edge v hv = some c := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 2 at hv; omega⟩⟩
  have hc := cycle_completion r h hd p hv hu
  have ht := walk_trace r h (fuel r) [] p (walk_not_exhausted r h _ _)
  have hs : (walk r h (fuel r) [] p).2 = .repeated p := hc.1
  rw [hs] at ht
  obtain ⟨ms,hm⟩ := cycleMatrices_trace r h vertex edge ht
  have hlen := cycleMatrices_length r h vertex edge _ ms hm
  have hmem := walk_start_mem r h (fuel r) (by dsimp [fuel]; omega) [] p (by simp)
  cases ms with
  | nil =>
    have he : (walk r h (fuel r) [] p).1 = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    simp [he] at hmem
  | cons M ms =>
    refine ⟨.cycle M ms,?_⟩
    simp [cycleFrom,p,hs,hm]

private theorem find_none {X : Type*} (P : X → Bool) (xs : List X)
    (hn : xs.find? P = none) : ∀ x ∈ xs, P x = false := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : P x with
    | true => simp [List.find?,hp] at hn
    | false =>
      have ht : xs.find? P = none := by simpa [List.find?,hp] using hn
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact ih ht y hy

theorem component_total (hd : ∀ v, degree (arity := arity) r v ≤ 2) (root : Fin r.vertices.length)
    (hr : root ∈ (r.graph h).roots) : ∃ c, component r h vertex edge root = some c := by
  have hroot := ((r.graph h).mem_roots root).mp hr
  cases hs : ((r.graph h).componentVertices root).find? (fun v => decide (degree (arity := arity) r v = 1)) with
  | some v =>
    have hv : degree (arity := arity) r v = 1 := of_decide_eq_true (show decide (degree (arity := arity) r v = 1) = true from List.find?_some (p := fun w : Fin r.vertices.length => decide (degree (arity := arity) r w = 1)) hs)
    obtain ⟨c,hc⟩ := pathFrom_total r h vertex edge hd v hv
    exact ⟨c,by simp only [component,hs,dif_pos hv]; exact hc⟩
  | none =>
    have hu : ∀ v, (r.graph h).label v = (r.graph h).label root → degree (arity := arity) r v ≠ 1 := by
      intro v hv
      have hm : v ∈ (r.graph h).componentVertices root := by
        rw [(r.graph h).mem_componentVertices]
        exact hv.trans hroot
      have hh := find_none (fun v => decide (degree (arity := arity) r v = 1)) _ hs v hm
      simpa only [decide_eq_false_iff_not] using hh
    by_cases hz : degree (arity := arity) r root = 0
    · exact ⟨.scalar (vertex root (fun _ => false)),by simp [component,hs,hz]⟩
    · have hb : degree (arity := arity) r root = 2 := by have hle := hd root; have hn := hu root rfl; omega
      obtain ⟨c,hc⟩ := cycleFrom_total r h vertex edge hd root hb hu
      exact ⟨c,by simp only [component,hs,if_neg hz,dif_pos hb]; exact hc⟩

theorem all_total (hd : ∀ v, degree (arity := arity) r v ≤ 2) : ∃ cs, all r h vertex edge = some cs := by
  have aux (roots : List (Fin r.vertices.length))
      (hr : ∀ root ∈ roots, root ∈ (r.graph h).roots) :
      ∃ cs, roots.mapM (component r h vertex edge) = some cs := by
    induction roots with
    | nil => exact ⟨[],rfl⟩
    | cons root roots ih =>
      obtain ⟨c,hc⟩ := component_total r h vertex edge hd root (hr root (by simp))
      obtain ⟨cs,hcs⟩ := ih (fun v hv => hr v (List.mem_cons_of_mem root hv))
      exact ⟨c::cs,by simp [hc,hcs]⟩
  exact aux _ (fun _ h => h)

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.Descriptors
